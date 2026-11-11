#!/usr/bin/env python3
"""MMA Comptabilité — comptabilité de trésorerie locale, dérivée de Dominis.

Le moteur, l'interface et les ressources sont centralisés dans ce fichier.
Les montants persistés sont des centimes entiers. Aucune base de démonstration
n'est créée dans le dossier utilisateur sans demande explicite.
"""
import argparse
import ast
import base64
import calendar
import csv
import datetime as dt
import hashlib
import html
import io
import json
import logging
import math
import mimetypes
import os
import platform
import re
import secrets
import shutil
import sqlite3
import ssl
import subprocess
import sys
import tempfile
import threading
import time
import uuid
import zipfile
import zlib
import xml.etree.ElementTree as ET
from contextlib import contextmanager
from decimal import Decimal, InvalidOperation
from http.server import ThreadingHTTPServer, BaseHTTPRequestHandler
from pathlib import Path
from urllib.parse import urlparse, parse_qs, quote
from urllib.request import Request, build_opener, HTTPRedirectHandler, HTTPSHandler

APP_VERSION = 'v1.0.0'
SCHEMA_VERSION = 1
# Migration n -> n+1 : fonction SQL transactionnelle, ajoutée lors d'une évolution.
# Aucun schéma historique n'est inventé pour cette première version.
MIGRATIONS = {}
APP_ID = 0x4D4D4131
APP_NAME = 'MMA Comptabilité'
REPO = 'astronix62/MMA-Comptabilite'
MAX_FILE = 30 * 1024 * 1024
MAX_CENTS = 100_000_000_000
LOCK = threading.RLock()
TOKEN = secrets.token_urlsafe(32)
WINDOW = None
SERVER = None
STORE = None
STOP = threading.Event()
READY = threading.Event()
UPDATE_LOCK = threading.Lock()
UPDATE = {'status': 'idle', 'message': '', 'current': APP_VERSION}
IMPORTS = {}


def uid(): return uuid.uuid4().hex
def now(): return dt.datetime.now(dt.timezone.utc).isoformat(timespec='seconds')


def data_directory():
    if sys.platform == 'win32':
        return Path(os.environ.get('LOCALAPPDATA', Path.home() / 'AppData/Local')) / 'MMA Comptabilite'
    if sys.platform == 'darwin': return Path.home() / 'Library/Application Support/MMA Comptabilite'
    return Path(os.environ.get('XDG_DATA_HOME', Path.home() / '.local/share')) / 'mma-comptabilite'


def money(value, allow_zero=True):
    """Conversion exacte ; refuse arrondis implicites, NaN et formats ambigus."""
    if isinstance(value, bool) or value is None: raise ValueError('Montant invalide.')
    text = re.sub(r'[\s\u00a0\u202f€]', '', str(value)).replace('−', '-')
    if ',' in text and '.' in text:
        if text.rfind(',') > text.rfind('.'): text = text.replace('.', '').replace(',', '.')
        else: text = text.replace(',', '')
    else: text = text.replace(',', '.')
    if not re.fullmatch(r'[+-]?\d+(?:\.\d{1,2})?', text):
        raise ValueError('Montant attendu avec au plus deux décimales (ex. 1234,56).')
    cents = int(Decimal(text) * 100)
    if abs(cents) > MAX_CENTS or (not allow_zero and not cents): raise ValueError('Montant nul ou hors limites.')
    return cents


def euro(cents): return f'{Decimal(cents) / 100:.2f}'


def valid_date(value):
    text = str(value or '').strip()
    for fmt in ('%Y-%m-%d', '%d/%m/%Y', '%d.%m.%Y', '%d-%m-%Y'):
        try:
            day = dt.datetime.strptime(text, fmt).date()
            if not 1900 <= day.year <= 2999: break
            return day.isoformat()
        except ValueError: pass
    raise ValueError('Date invalide : AAAA-MM-JJ ou JJ/MM/AAAA attendue.')


def text_field(value, label, limit=250, required=True):
    v = str(value or '').strip()
    if (required and not v) or len(v) > limit or '\x00' in v:
        raise ValueError(f'{label} : valeur manquante ou trop longue (maximum {limit}).')
    return v


DEFAULT_CATEGORIES = [
    ('Cotisations', 'Recette'), ('Subventions', 'Recette'), ('Dons', 'Recette'),
    ('Sponsoring', 'Recette'), ('Stages et événements', 'Recette'), ('Ventes', 'Recette'),
    ('Autres recettes', 'Recette'), ('Licences et affiliations', 'Dépense'),
    ('Matériel sportif', 'Dépense'), ('Location et charges', 'Dépense'),
    ('Assurances', 'Dépense'), ('Déplacements', 'Dépense'), ('Intervenants', 'Dépense'),
    ('Frais bancaires', 'Dépense'), ('Communication', 'Dépense'), ('Autres dépenses', 'Dépense')]

SCHEMA = '''
CREATE TABLE meta(key TEXT PRIMARY KEY, value TEXT NOT NULL);
CREATE TABLE accounts(id TEXT PRIMARY KEY, name TEXT NOT NULL UNIQUE, opening INTEGER NOT NULL CHECK(typeof(opening)='integer'), opening_date TEXT NOT NULL, active INTEGER NOT NULL DEFAULT 1 CHECK(active IN (0,1)));
CREATE TABLE categories(id TEXT PRIMARY KEY, name TEXT NOT NULL, direction TEXT NOT NULL CHECK(direction IN ('Recette','Dépense')), active INTEGER NOT NULL DEFAULT 1 CHECK(active IN (0,1)), UNIQUE(name,direction));
CREATE TABLE periods(id TEXT PRIMARY KEY, name TEXT NOT NULL, start TEXT NOT NULL, end TEXT NOT NULL, closed INTEGER NOT NULL DEFAULT 0 CHECK(closed IN (0,1)), CHECK(start<=end));
CREATE TABLE entries(id TEXT PRIMARY KEY, date TEXT NOT NULL, label TEXT NOT NULL, amount INTEGER NOT NULL CHECK(typeof(amount)='integer' AND amount>0 AND amount<=100000000000), direction TEXT NOT NULL CHECK(direction IN ('Recette','Dépense','Virement')), account_id TEXT NOT NULL REFERENCES accounts(id), target_id TEXT REFERENCES accounts(id), category_id TEXT REFERENCES categories(id), payment TEXT NOT NULL, reference TEXT NOT NULL DEFAULT '', notes TEXT NOT NULL DEFAULT '', cleared INTEGER NOT NULL DEFAULT 0 CHECK(cleared IN (0,1)), revision INTEGER NOT NULL DEFAULT 1, created TEXT NOT NULL, CHECK((direction='Virement' AND target_id IS NOT NULL AND target_id<>account_id AND category_id IS NULL) OR (direction<>'Virement' AND target_id IS NULL AND category_id IS NOT NULL)));
CREATE INDEX entries_date ON entries(date);
CREATE INDEX entries_account ON entries(account_id,date);
CREATE TABLE documents(id TEXT PRIMARY KEY, entry_id TEXT REFERENCES entries(id) ON DELETE SET NULL, name TEXT NOT NULL, folder TEXT NOT NULL, filename TEXT NOT NULL, mime TEXT NOT NULL, sha256 TEXT NOT NULL, data BLOB NOT NULL, created TEXT NOT NULL);
CREATE TABLE budgets(id TEXT PRIMARY KEY, period_id TEXT NOT NULL REFERENCES periods(id), category_id TEXT NOT NULL REFERENCES categories(id), amount INTEGER NOT NULL CHECK(typeof(amount)='integer' AND amount>=0), UNIQUE(period_id,category_id));
CREATE TABLE audit(id INTEGER PRIMARY KEY AUTOINCREMENT, at TEXT NOT NULL, action TEXT NOT NULL, detail TEXT NOT NULL);
CREATE TABLE imports(fingerprint TEXT PRIMARY KEY, at TEXT NOT NULL);
'''


class Store:
    def __init__(self, folder):
        self.folder = Path(folder).resolve()
        self.folder.mkdir(parents=True, exist_ok=True)
        self.path = self.folder / 'Data.db'
        self.backups = self.folder / 'sauvegardes'
        self.backups.mkdir(exist_ok=True)
        self.backup_error = ''
        self.recovery = not self.path.exists() and bool(list(self.backups.glob('*.db')))
        self.initialize()

    @contextmanager
    def db(self):
        c = sqlite3.connect(self.path, timeout=20)
        c.row_factory = sqlite3.Row
        c.execute('PRAGMA foreign_keys=ON')
        c.execute('PRAGMA synchronous=FULL')
        try:
            yield c
            c.commit()
        except BaseException:
            c.rollback()
            raise
        finally: c.close()

    def initialize(self):
        existing = self.path.exists() and self.path.stat().st_size > 0
        if existing:
            with self.db() as c:
                if c.execute('PRAGMA application_id').fetchone()[0] != APP_ID:
                    raise ValueError('Data.db ne provient pas de MMA Comptabilité. Aucun écrasement effectué.')
                version = c.execute('PRAGMA user_version').fetchone()[0]
                recovery=c.execute("SELECT value FROM meta WHERE key='recovery_required'").fetchone()
                self.recovery=bool(recovery and recovery[0]=='1')
                if version > SCHEMA_VERSION: raise ValueError('Base créée par une version plus récente. Mettez le logiciel à jour.')
                if version < SCHEMA_VERSION:
                    if any(v not in MIGRATIONS for v in range(version,SCHEMA_VERSION)):
                        raise ValueError('Migration non disponible pour cette ancienne structure. Base conservée.')
                    self.validate(c,version)
                else: self.validate(c)
            if version < SCHEMA_VERSION:
                self.backup('avant-migration',expected_version=version)
                with self.db() as c:
                    c.execute('BEGIN IMMEDIATE')
                    for old in range(version,SCHEMA_VERSION):
                        MIGRATIONS[old](c)
                        c.execute(f'PRAGMA user_version={old+1}')
                    self.validate(c)
                    self.audit(c,'Migration',{'de':version,'vers':SCHEMA_VERSION})
            return
        with self.db() as c:
            c.executescript('BEGIN IMMEDIATE;\n' + SCHEMA)
            c.execute(f'PRAGMA application_id={APP_ID}')
            c.execute(f'PRAGMA user_version={SCHEMA_VERSION}')
            c.execute('INSERT INTO meta VALUES(?,?)', ('settings', json.dumps({'theme': 'dark', 'density': 'normal', 'owner': 'MMA Fight Club Calais'})))
            if self.recovery: c.execute('INSERT INTO meta VALUES(?,?)',('recovery_required','1'))
            c.execute('INSERT INTO accounts VALUES(?,?,?,?,1)', ('bank', 'Compte bancaire', 0, '1900-01-01'))
            c.execute('INSERT INTO accounts VALUES(?,?,?,?,1)', ('cash', 'Caisse', 0, '1900-01-01'))
            for name, direction in DEFAULT_CATEGORIES:
                c.execute('INSERT INTO categories VALUES(?,?,?,1)', (uid(), name, direction))
            year = dt.date.today().year
            c.execute('INSERT INTO periods VALUES(?,?,?,?,0)', (uid(), str(year), f'{year}-01-01', f'{year}-12-31'))
            self.audit(c, 'Création', 'Espace comptable vierge')

    @staticmethod
    def audit(c, action, detail):
        c.execute('INSERT INTO audit(at,action,detail) VALUES(?,?,?)', (now(), action, json.dumps(detail, ensure_ascii=False)))

    @staticmethod
    def validate(c, expected_version=None):
        expected_version=SCHEMA_VERSION if expected_version is None else expected_version
        if c.execute('PRAGMA application_id').fetchone()[0] != APP_ID or c.execute('PRAGMA user_version').fetchone()[0] != expected_version:
            raise ValueError('Version ou application de la sauvegarde incompatible.')
        if c.execute('PRAGMA integrity_check').fetchone()[0] != 'ok' or c.execute('PRAGMA foreign_key_check').fetchone():
            raise ValueError('Échec du contrôle d’intégrité SQLite.')
        expected = {'meta','accounts','categories','periods','entries','documents','budgets','audit','imports'}
        found = {r[0] for r in c.execute("SELECT name FROM sqlite_master WHERE type='table'")}
        if not expected <= found: raise ValueError('Sauvegarde incomplète.')
        if c.execute("SELECT 1 FROM sqlite_master WHERE type IN ('trigger','view')").fetchone(): raise ValueError('Structure inattendue : restauration refusée.')
        prefs = json.loads(c.execute("SELECT value FROM meta WHERE key='settings'").fetchone()[0])
        if not isinstance(prefs, dict): raise ValueError('Paramètres invalides.')
        periods = list(c.execute('SELECT * FROM periods ORDER BY start'))
        for i, p in enumerate(periods):
            valid_date(p['start']); valid_date(p['end'])
            if p['start'] > p['end'] or (i and periods[i-1]['end'] >= p['start']): raise ValueError('Exercices incohérents.')
        for a in c.execute('SELECT * FROM accounts'):
            valid_date(a['opening_date'])
            if type(a['opening']) is not int or abs(a['opening']) > MAX_CENTS: raise ValueError('Solde initial invalide.')
        for e in c.execute('SELECT * FROM entries'):
            valid_date(e['date'])
            if type(e['amount']) is not int or not 0 < e['amount'] <= MAX_CENTS: raise ValueError('Montant incohérent.')
            if not any(p['start'] <= e['date'] <= p['end'] for p in periods): raise ValueError('Opération hors exercice.')
            a = c.execute('SELECT opening_date FROM accounts WHERE id=?', (e['account_id'],)).fetchone()
            if e['date'] < a[0]: raise ValueError('Opération antérieure au solde initial.')
            if e['direction'] == 'Virement':
                target = c.execute('SELECT opening_date FROM accounts WHERE id=?', (e['target_id'],)).fetchone()
                if not target or e['target_id'] == e['account_id'] or e['category_id'] is not None or e['date'] < target[0]: raise ValueError('Virement incohérent.')
            else:
                cat = c.execute('SELECT direction FROM categories WHERE id=?', (e['category_id'],)).fetchone()
                if not cat or cat[0] != e['direction'] or e['target_id'] is not None: raise ValueError('Catégorie incohérente.')
        for d in c.execute('SELECT sha256,data FROM documents'):
            if hashlib.sha256(d['data']).hexdigest() != d['sha256']: raise ValueError('Justificatif endommagé.')

    def backup(self, reason='manuel', expected_version=None):
        with LOCK:
            if self.recovery and reason in ('auto','fermeture'):
                raise ValueError('Base principale absente : restaurez une sauvegarde. Les copies existantes sont conservées sans rotation.')
            name = dt.datetime.now().strftime('%Y%m%d-%H%M%S-%f') + '-' + reason + '.db'
            target = self.backups / name
            temp = target.with_suffix('.tmp')
            try:
                with self.db() as src:
                    self.validate(src,expected_version)
                    dst = sqlite3.connect(temp)
                    try: src.backup(dst)
                    finally: dst.close()
                check = sqlite3.connect(temp); check.row_factory = sqlite3.Row
                try: self.validate(check,expected_version)
                finally: check.close()
                with temp.open('rb+') as f: os.fsync(f.fileno())
                os.replace(temp, target)
                self.backup_error = ''
                # Seules les sauvegardes périodiques sont purgées, après validation.
                auto = sorted(self.backups.glob('*-auto.db'))
                for old in auto[:-48]: old.unlink()
                return target
            finally: temp.unlink(missing_ok=True)

    def restore(self, raw, confirmation):
        if confirmation != 'RESTAURER': raise ValueError('Saisissez RESTAURER pour confirmer.')
        if len(raw) > 500*1024*1024 or not raw.startswith(b'SQLite format 3\0'): raise ValueError('Sauvegarde SQLite invalide.')
        with LOCK:
            temp = self.folder / ('.restore-' + uid() + '.db')
            try:
                temp.write_bytes(raw)
                src = sqlite3.connect(f'{temp.as_uri()}?mode=ro', uri=True); src.row_factory = sqlite3.Row
                try:
                    self.validate(src)
                    # Copie des données dans le schéma connu, jamais du SQL importé.
                    tables = ['meta','accounts','categories','periods','entries','documents','budgets','audit','imports']
                    rows = {t: [dict(r) for r in src.execute('SELECT * FROM ' + t)] for t in tables}
                finally: src.close()
                self.backup('avant-restauration')
                with self.db() as dst:
                    dst.execute('BEGIN IMMEDIATE')
                    for t in reversed(tables): dst.execute('DELETE FROM ' + t)
                    for t in tables:
                        columns = [r[1] for r in dst.execute('PRAGMA table_info(' + t + ')')]
                        for r in rows[t]:
                            if set(columns) != set(r): raise ValueError('Colonnes de sauvegarde incompatibles.')
                            dst.execute('INSERT INTO ' + t + ' VALUES(' + ','.join('?' for _ in columns) + ')', [r[k] for k in columns])
                    self.validate(dst)
                    self.audit(dst, 'Restauration', 'Copie de précaution conservée')
                IMPORTS.clear()
                self.recovery = False
            finally: temp.unlink(missing_ok=True)

    def assert_open(self, c, date):
        p = c.execute('SELECT * FROM periods WHERE start<=? AND end>=?', (date,date)).fetchone()
        if not p: raise ValueError('Créez un exercice couvrant cette date.')
        if p['closed']: raise ValueError('Cet exercice est clôturé : écriture interdite.')

    def normalize_entry(self, c, p):
        date = valid_date(p.get('date'))
        self.assert_open(c, date)
        direction = p.get('direction')
        if direction not in ('Recette','Dépense','Virement'): raise ValueError('Sens invalide.')
        amount = money(p.get('amount'), False)
        if amount < 0: raise ValueError('Utilisez un montant positif et choisissez le sens.')
        account = c.execute('SELECT * FROM accounts WHERE id=?', (p.get('account_id'),)).fetchone()
        if not account or not account['active']: raise ValueError('Compte indisponible.')
        if date < account['opening_date']: raise ValueError('Date antérieure au solde initial du compte.')
        target = None; category = None
        if direction == 'Virement':
            target = p.get('target_id')
            a = c.execute('SELECT * FROM accounts WHERE id=?', (target,)).fetchone()
            if not a or not a['active'] or target == account['id'] or date < a['opening_date']: raise ValueError('Compte destinataire invalide.')
        else:
            category = p.get('category_id')
            cat = c.execute('SELECT * FROM categories WHERE id=? AND active=1', (category,)).fetchone()
            if not cat or cat['direction'] != direction: raise ValueError('Catégorie incompatible avec le sens.')
        return {'date':date,'label':text_field(p.get('label'),'Libellé'), 'amount':amount,'direction':direction,
                'account_id':account['id'],'target_id':target,'category_id':category,
                'payment':text_field(p.get('payment','Virement'),'Moyen de paiement',60),
                'reference':text_field(p.get('reference'),'Référence',100,False),
                'notes':text_field(p.get('notes'),'Notes',5000,False), 'cleared':int(p.get('cleared') in (True,1,'1'))}

    def save_entry(self, p, connection=None):
        if self.recovery: raise ValueError('Restaurez les données manquantes avant toute nouvelle saisie.')
        if connection is None:
            with LOCK, self.db() as c: return self.save_entry(p,c)
        c = connection
        previous = c.execute('SELECT * FROM entries WHERE id=?', (p.get('id',''),)).fetchone()
        if p.get('id') and not previous: raise ValueError('Opération supprimée : rechargez la liste.')
        if previous:
            self.assert_open(c, previous['date'])
            if p.get('revision') != previous['revision']: raise ValueError('Opération modifiée depuis son ouverture. Rechargez-la.')
        d = self.normalize_entry(c,p)
        ident = p.get('id') or uid()
        if previous:
            c.execute('UPDATE entries SET ' + ','.join(k+'=?' for k in d) + ',revision=revision+1 WHERE id=?', [*d.values(),ident])
        else:
            c.execute('INSERT INTO entries(id,'+','.join(d)+',created) VALUES('+','.join('?' for _ in range(len(d)+2))+')',[ident,*d.values(),now()])
        self.audit(c, 'Modification opération' if previous else 'Création opération', {'id':ident,'avant':dict(previous) if previous else None,'après':d})
        return ident

    def state(self):
        with LOCK, self.db() as c:
            out = {t:[dict(r) for r in c.execute('SELECT * FROM '+t)] for t in ('accounts','categories','periods','entries','budgets')}
            out['documents'] = [dict(r) for r in c.execute('SELECT id,entry_id,name,folder,filename,mime,sha256,length(data) size,created FROM documents')]
            out['audit'] = [dict(r) for r in c.execute('SELECT * FROM audit ORDER BY id DESC LIMIT 200')]
            out['settings'] = json.loads(c.execute("SELECT value FROM meta WHERE key='settings'").fetchone()[0])
        out.update(version=APP_VERSION, data_path=str(self.path), native=WINDOW is not None, backup_error=self.backup_error, recovery=self.recovery)
        out['backups'] = [{'name':p.name,'size':p.stat().st_size} for p in sorted(self.backups.glob('*.db'),reverse=True)[:100]]
        return out

    def mutate(self, action, p):
        with LOCK:
            if self.recovery and action!='settings': raise ValueError('Restaurez les données manquantes avant toute modification.')
            if action == 'entry': return {'id':self.save_entry(p)}
            if action in ('delete-entry','close-period','reopen-period'):
                if p.get('confirmation') != 'CONFIRMER': raise ValueError('Confirmation requise.')
                self.backup('avant-'+action)
            with self.db() as c:
                if action == 'delete-entry':
                    old = c.execute('SELECT * FROM entries WHERE id=?',(p.get('id'),)).fetchone()
                    if not old: raise ValueError('Opération introuvable.')
                    self.assert_open(c,old['date'])
                    if p.get('revision') != old['revision']: raise ValueError('Opération modifiée : rechargez-la.')
                    c.execute('DELETE FROM entries WHERE id=?',(old['id'],))
                    self.audit(c,'Suppression opération',dict(old))
                elif action == 'account':
                    ident = p.get('id') or uid()
                    old = c.execute('SELECT * FROM accounts WHERE id=?',(ident,)).fetchone()
                    name = text_field(p.get('name'),'Nom',80)
                    opening = money(p.get('opening','0')); day = valid_date(p.get('opening_date','1900-01-01'))
                    if old and (opening != old['opening'] or day != old['opening_date']):
                        if c.execute('SELECT 1 FROM entries WHERE account_id=? OR target_id=?',(ident,ident)).fetchone():
                            raise ValueError('Solde initial verrouillé après la première opération. Utilisez une écriture corrective.')
                    c.execute('INSERT INTO accounts VALUES(?,?,?,?,?) ON CONFLICT(id) DO UPDATE SET name=excluded.name,opening=excluded.opening,opening_date=excluded.opening_date,active=excluded.active',(ident,name,opening,day,int(p.get('active',1) in (1,True,'1'))))
                    self.audit(c,'Compte',{'avant':dict(old) if old else None,'après':p})
                elif action == 'category':
                    ident = p.get('id') or uid(); direction = p.get('direction')
                    if direction not in ('Recette','Dépense'): raise ValueError('Sens invalide.')
                    old = c.execute('SELECT * FROM categories WHERE id=?',(ident,)).fetchone()
                    if old and old['direction'] != direction and c.execute('SELECT 1 FROM entries WHERE category_id=?',(ident,)).fetchone(): raise ValueError('Sens verrouillé : catégorie déjà utilisée.')
                    c.execute('INSERT INTO categories VALUES(?,?,?,?) ON CONFLICT(id) DO UPDATE SET name=excluded.name,direction=excluded.direction,active=excluded.active',(ident,text_field(p.get('name'),'Nom',80),direction,int(p.get('active',1) in (1,True,'1'))))
                    self.audit(c,'Catégorie',p)
                elif action == 'period':
                    start,end = valid_date(p.get('start')),valid_date(p.get('end'))
                    if start > end or c.execute('SELECT 1 FROM periods WHERE start<=? AND end>=?',(end,start)).fetchone(): raise ValueError('Dates inversées ou exercices qui se chevauchent.')
                    c.execute('INSERT INTO periods VALUES(?,?,?,?,0)',(uid(),text_field(p.get('name'),'Nom',80),start,end))
                    self.audit(c,'Création exercice',p)
                elif action in ('close-period','reopen-period'):
                    period = c.execute('SELECT * FROM periods WHERE id=?',(p.get('id'),)).fetchone()
                    if not period: raise ValueError('Exercice introuvable.')
                    self.validate(c)
                    if action == 'reopen-period': text_field(p.get('reason'),'Motif de réouverture',500)
                    c.execute('UPDATE periods SET closed=? WHERE id=?',(int(action=='close-period'),period['id']))
                    self.audit(c,'Clôture' if action=='close-period' else 'Réouverture',p)
                elif action == 'budget':
                    period = c.execute('SELECT * FROM periods WHERE id=?',(p.get('period_id'),)).fetchone()
                    if not period or period['closed']: raise ValueError('Exercice absent ou clôturé.')
                    amt = money(p.get('amount'))
                    if amt < 0: raise ValueError('Budget négatif interdit.')
                    c.execute('INSERT INTO budgets VALUES(?,?,?,?) ON CONFLICT(period_id,category_id) DO UPDATE SET amount=excluded.amount',(uid(),period['id'],p.get('category_id'),amt))
                    self.audit(c,'Budget',p)
                elif action == 'settings':
                    st = json.loads(c.execute("SELECT value FROM meta WHERE key='settings'").fetchone()[0])
                    if 'theme' in p and p['theme'] in ('dark','light'): st['theme']=p['theme']
                    if 'density' in p and p['density'] in ('normal','compact'): st['density']=p['density']
                    if 'motion' in p and p['motion'] in ('auto','off'): st['motion']=p['motion']
                    if 'owner' in p: st['owner']=text_field(p['owner'],'Nom du club',100)
                    c.execute("UPDATE meta SET value=? WHERE key='settings'",(json.dumps(st),))
                elif action == 'document':
                    raw = decode_file(p.get('blob',''))
                    filename = Path(p.get('filename','')).name
                    if not filename: raise ValueError('Nom de fichier manquant.')
                    entry = p.get('entry_id') or None
                    if entry:
                        e = c.execute('SELECT date FROM entries WHERE id=?',(entry,)).fetchone()
                        if not e: raise ValueError('Opération introuvable.')
                        self.assert_open(c,e[0])
                    ident=uid()
                    c.execute('INSERT INTO documents VALUES(?,?,?,?,?,?,?,?,?)',(ident,entry,text_field(p.get('name') or filename,'Titre'),text_field(p.get('folder','Justificatifs'),'Dossier',80),filename,mimetypes.guess_type(filename)[0] or 'application/octet-stream',hashlib.sha256(raw).hexdigest(),raw,now()))
                    self.audit(c,'Ajout justificatif',{'id':ident,'filename':filename,'entry':entry})
                else: raise ValueError('Action inconnue.')
            return {'ok':True}


def decode_file(blob, limit=MAX_FILE):
    if not isinstance(blob,str) or len(blob)>limit*4//3+8: raise ValueError('Fichier trop volumineux.')
    try: raw=base64.b64decode(blob,validate=True)
    except Exception: raise ValueError('Encodage de fichier invalide.')
    if not raw or len(raw)>limit: raise ValueError('Fichier vide ou trop volumineux.')
    return raw


def safe_zip(raw):
    with zipfile.ZipFile(io.BytesIO(raw)) as z:
        if len(z.infolist())>10000 or sum(x.file_size for x in z.infolist())>100*1024*1024:
            raise ValueError('Archive trop volumineuse après décompression.')
        for x in z.infolist():
            if x.flag_bits & 1: raise ValueError('Archive chiffrée non prise en charge.')


def clean(kind, data):
    """Adaptateur du lecteur tabulaire Dominis : aucune écriture ni catégorie devinée."""
    d=dict(data)
    d['date']=valid_date(d.get('date'))
    d['label']=text_field(d.get('label'),'Libellé')
    # Le lecteur historique produit parfois un float ; retour décimal explicite.
    d['amount']=euro(money(str(d.get('amount'))))
    return d


def read_import(p):
    raw=decode_file(p.get('blob','')); ext=Path(p.get('filename','')).suffix.lower()
    warnings=[]; rows=[]; headers=[]; cells=[]
    if ext in ('.xlsx','.docx'): safe_zip(raw)
    if ext=='.xlsx' and p.get('auto_tables'):
        b=parse_xlsx(base64.b64encode(raw).decode())
        rows=b['records']; warnings=b.get('warnings',[])
        warnings.append('Lecteur de tableaux Dominis : vérifiez toutes les propositions et les soldes signalés. Les soldes initiaux ne sont jamais appliqués automatiquement.')
        return rows,warnings,[],[]
    if ext=='.json':
        b=json.loads(raw.decode('utf-8-sig'),parse_float=Decimal)
        if isinstance(b,dict) and b.get('application') in ('Dominis','Aurea','MMA Comptabilité'):
            rows=b.get('entries',b.get('records',[]))
            rows=[r for r in rows if r.get('kind','entries')=='entries']
            warnings.append('Import des mouvements uniquement : comptes et catégories à vérifier. Pour restaurer tout l’espace, utilisez une sauvegarde Data.db.')
            if b.get('application')=='MMA Comptabilité':
                rows=[{**r,'amount':euro(r['amount'])} for r in rows]
            return rows,warnings,[],[]
        raise ValueError('Export JSON MMA Comptabilité ou Dominis attendu.')
    if ext in ('.pdf','.txt'):
        if ext=='.pdf':
            from pypdf import PdfReader
            pdf=PdfReader(io.BytesIO(raw))
            if pdf.is_encrypted or len(pdf.pages)>100: raise ValueError('PDF protégé ou supérieur à 100 pages.')
            texts=[(i+1,page.extract_text(extraction_mode='layout') or '') for i,page in enumerate(pdf.pages)]
        else: texts=[(1,decode_text(raw))]
        for page,text in texts:
            if not text.strip(): warnings.append(f'Page {page} : aucun texte lisible. Scan sans OCR ; saisie manuelle nécessaire.')
            for row in statement_lines(text,page):
                if not row.get('context'): rows.append(row)
        warnings.append('Lecture de relevé indicative : vérifiez le sens, les dates et chaque montant avec le document original. Les lignes de solde ne sont pas des opérations.')
        return rows,warnings,[],[]
    if ext=='.xlsx':
        from openpyxl import load_workbook
        book=load_workbook(io.BytesIO(raw),read_only=True,data_only=True)
        try:
            sheet=p.get('sheet') or book.sheetnames[0]
            if sheet not in book.sheetnames: raise ValueError('Feuille introuvable.')
            cells=[]
            for r in book[sheet].iter_rows(values_only=True):
                if len(cells)>=10001: raise ValueError('Import limité à 10 000 lignes.')
                cells.append([v.isoformat()[:10] if isinstance(v,(dt.date,dt.datetime)) else '' if v is None else str(v) for v in r])
            warnings.append('Feuille '+sheet+' ; autres feuilles : '+', '.join(book.sheetnames)+'. Formules : valeurs enregistrées par Excel uniquement ; utilisez le lecteur de tableaux pour ses contrôles avancés.')
        finally: book.close()
    elif ext in ('.csv','.tsv'):
        text=decode_text(raw)
        try: dialect=csv.Sniffer().sniff(text[:8000],delimiters=';,\t')
        except csv.Error: dialect=csv.excel_tab if ext=='.tsv' else csv.excel
        cells=list(csv.reader(io.StringIO(text),dialect))
    else: raise ValueError('Formats : CSV, TSV, XLSX, JSON, PDF et TXT. Les images et DOCX peuvent être conservés comme justificatifs.')
    if not cells or len(cells)>10001: raise ValueError('Fichier vide ou supérieur à 10 000 lignes.')
    header_row=int(p.get('header_row',1))
    if not 1<=header_row<=len(cells): raise ValueError('Ligne d’en-tête invalide.')
    headers=cells[header_row-1]
    mapping=p.get('mapping') or {}
    aliases={'date':['date','date operation','date d operation'],'label':['libelle','label','description'], 'amount':['montant','amount'], 'direction':['sens','direction'], 'debit':['debit'], 'credit':['credit'], 'reference':['reference','numero'], 'category':['categorie','category']}
    for key,names in aliases.items():
        if not mapping.get(key):
            mapping[key]=next((str(i) for i,h in enumerate(headers) if _x_norm(h) in names),'')
    for number,cell in enumerate(cells[header_row:],header_row+1):
        if not any(str(x).strip() for x in cell): continue
        row={'source':f'Ligne {number} : '+' | '.join(cell)}
        for key,index in mapping.items():
            if str(index).isdigit() and int(index)<len(cell): row[key]=cell[int(index)]
        if row.get('debit') or row.get('credit'):
            try:
                debit=money(row.get('debit') or '0'); credit=money(row.get('credit') or '0')
                if debit and credit: raise ValueError('Débit et crédit renseignés sur la même ligne.')
                if debit<0 or credit<0: raise ValueError('Débit/crédit négatif : vérifiez le sens.')
                row.update(amount=euro(debit or credit),direction='Dépense' if debit else 'Recette')
            except ValueError as e: row['parse_error']=str(e)
        elif row.get('amount'):
            try:
                amt=money(row['amount'])
                if not row.get('direction'): row['direction']='Dépense' if amt<0 else 'Recette'
                row['amount']=euro(abs(amt))
            except ValueError as e: row['parse_error']=str(e)
        rows.append(row)
    return rows,warnings,headers,cells[header_row:header_row+5]


def decode_text(raw):
    try: return raw.decode('utf-8-sig')
    except UnicodeDecodeError: return raw.decode('cp1252')


def entry_signature(e):
    return (e['date'],_x_norm(e['label']),e['amount'],e['direction'],e['account_id'],e.get('target_id'))


def preview_import(p):
    rows,warnings,headers,sample=read_import(p)
    if len(rows)>10000: raise ValueError('Import limité à 10 000 opérations.')
    output=[]
    with LOCK,STORE.db() as c:
        cats=[dict(r) for r in c.execute('SELECT * FROM categories WHERE active=1')]
        seen={entry_signature(dict(e)) for e in c.execute('SELECT * FROM entries')}
        for row in rows:
            direction=row.get('direction','')
            direction={'recette':'Recette','credit':'Recette','depense':'Dépense','debit':'Dépense','virement':'Virement'}.get(_x_norm(direction),direction)
            category=next((x['id'] for x in cats if _x_norm(x['name'])==_x_norm(row.get('category','')) and x['direction']==direction),p.get('category_id',''))
            d={**row,'account_id':p.get('account_id','bank'),'category_id':category,'direction':direction,'amount':str(row.get('amount',''))}
            if p.get('direction'): d['direction']=p['direction']
            errors=[]
            if row.get('parse_error'): errors.append(row['parse_error'])
            try:
                d['date']=valid_date(d.get('date'))
                normalized=STORE.normalize_entry(c,d)
                duplicate=entry_signature(normalized) in seen
                seen.add(entry_signature(normalized))
            except ValueError as e: errors.append(str(e)); duplicate=False
            output.append({**d,'errors':errors,'duplicate':duplicate,'selected':not errors and not duplicate})
    return {'rows':output,'warnings':warnings,'headers':headers,'sample':sample}


def commit_import(p):
    if p.get('confirmation') != 'IMPORTER': raise ValueError('Confirmation explicite requise.')
    rows=p.get('rows')
    if not isinstance(rows,list) or not 0<len(rows)<=10000: raise ValueError('Sélectionnez les opérations à importer.')
    with LOCK:
        STORE.backup('avant-import')
        with STORE.db() as c:
            c.execute('BEGIN IMMEDIATE')
            normalized=[STORE.normalize_entry(c,r) for r in rows]
            signatures={entry_signature(dict(r)) for r in c.execute('SELECT * FROM entries')}
            added=0; skipped=0
            for row,n in zip(rows,normalized):
                sig=entry_signature(n)
                if sig in signatures: skipped+=1; continue
                STORE.save_entry({k:v for k,v in row.items() if k not in ('id','revision')},c)
                signatures.add(sig); added+=1
            STORE.audit(c,'Import confirmé',{'ajoutées':added,'doublons ignorés':skipped})
        return {'added':added,'skipped':skipped}


def recurrence_preview(p):
    """Fréquences et fin de mois repris de Dominis, validation comptable par ligne."""
    count=p.get('count'); interval=p.get('interval'); unit=p.get('unit')
    if type(count) is not int or type(interval) is not int or not 1<=count<=120 or not 1<=interval<=24 or unit not in ('week','month','year'):
        raise ValueError('Série : 1 à 120 occurrences, intervalle de 1 à 24 semaines, mois ou années.')
    start=dt.date.fromisoformat(valid_date(p.get('start')))
    with LOCK,STORE.db() as c:
        source=c.execute('SELECT * FROM entries WHERE id=?',(p.get('id'),)).fetchone()
        if not source: raise ValueError('Opération introuvable.')
        rows=[]
        for i in range(count):
            if unit=='week': day=start+dt.timedelta(weeks=i*interval)
            else:
                month=start.year*12+start.month-1+i*interval*(12 if unit=='year' else 1)
                year,month=divmod(month,12);month+=1
                day=dt.date(year,month,min(start.day,calendar.monthrange(year,month)[1]))
            row={**dict(source),'date':day.isoformat(),'amount':euro(source['amount']),'cleared':0}
            row.pop('id');row.pop('revision')
            try: STORE.normalize_entry(c,row);error=''
            except ValueError as exc: error=str(exc)
            rows.append({**row,'error':error})
    return {'rows':rows}


def version_tuple(value):
    if not isinstance(value,str) or not re.fullmatch(r'v(0|[1-9]\d{0,5})\.(0|[1-9]\d{0,5})\.(0|[1-9]\d{0,5})',value):
        raise ValueError('Version stable attendue : vMAJEUR.MINEUR.CORRECTIF.')
    return tuple(map(int,value[1:].split('.')))


def platform_asset(system=None, machine=None, frozen=None):
    system=system or sys.platform; machine=(machine or platform.machine()).lower()
    frozen=getattr(sys,'frozen',False) if frozen is None else frozen
    if not frozen: return 'MMA_Comptabilite.py'
    arch={'amd64':'x64','x86_64':'x64','arm64':'arm64','aarch64':'arm64'}.get(machine)
    if not arch or system not in ('win32','darwin'): raise ValueError('Plateforme non prise en charge pour les mises à jour.')
    return f'MMA-Comptabilite-{ "windows" if system=="win32" else "macos"}-{arch}.{ "exe" if system=="win32" else "zip"}'


def validate_github_url(url):
    p=urlparse(url)
    if p.scheme!='https' or p.hostname not in ('api.github.com','github.com','release-assets.githubusercontent.com','objects.githubusercontent.com') or p.username or p.password or p.port not in (None,443):
        raise ValueError('Adresse GitHub non autorisée.')


class GitHubRedirects(HTTPRedirectHandler):
    def redirect_request(self,req,fp,code,msg,headers,newurl):
        validate_github_url(newurl)
        return super().redirect_request(req,fp,code,msg,headers,newurl)


def github_download(url,limit=2*1024*1024,target=None):
    validate_github_url(url)
    context=ssl.create_default_context()
    try:
        import certifi
        context.load_verify_locations(certifi.where())
    except ImportError: pass
    req=Request(url,headers={'User-Agent':'MMA-Comptabilite/'+APP_VERSION,'Accept':'application/octet-stream' if target else 'application/vnd.github+json'})
    with build_opener(GitHubRedirects(),HTTPSHandler(context=context)).open(req,timeout=15) as response:
        validate_github_url(response.url)
        if int(response.headers.get('Content-Length','0'))>limit: raise ValueError('Téléchargement trop volumineux.')
        output=open(target,'wb') if target else io.BytesIO()
        try:
            total=0; deadline=time.monotonic()+600
            while True:
                chunk=response.read(65536)
                if not chunk: break
                total+=len(chunk)
                if total>limit or time.monotonic()>deadline: raise ValueError('Téléchargement interrompu : limite dépassée.')
                output.write(chunk)
            if target: output.flush(); os.fsync(output.fileno()); return total
            return output.getvalue()
        finally: output.close()


def release_info(data, asset_name=None):
    if not isinstance(data,dict) or data.get('draft') or data.get('prerelease'): raise ValueError('Release non stable.')
    tag=data.get('tag_name'); version_tuple(tag)
    name=asset_name or platform_asset()
    assets=[a for a in data.get('assets',[]) if a.get('name')==name and a.get('state')=='uploaded']
    if len(assets)!=1: raise ValueError('Distribution manquante pour cet ordinateur : '+name)
    a=assets[0]; expected=f'https://github.com/{REPO}/releases/download/{tag}/{name}'
    if a.get('browser_download_url')!=expected: raise ValueError('Fichier hors du dépôt officiel.')
    if type(a.get('size')) is not int or not 0<a['size']<=400*1024*1024: raise ValueError('Taille invalide.')
    digest=a.get('digest','')
    if not re.fullmatch('sha256:[0-9a-fA-F]{64}',digest): raise ValueError('Empreinte SHA-256 GitHub absente : installation refusée.')
    return {'version':tag,'url':expected,'size':a['size'],'digest':digest[7:].lower(),'name':name}


def check_updates():
    if not UPDATE_LOCK.acquire(False): return
    try:
        UPDATE.update(status='checking',message='Vérification GitHub…')
        data=json.loads(github_download(f'https://api.github.com/repos/{REPO}/releases/latest'))
        tag=data.get('tag_name'); version_tuple(tag)
        if data.get('draft') or data.get('prerelease'): raise ValueError('Release non stable.')
        if version_tuple(tag)<=version_tuple(APP_VERSION): UPDATE.update(status='current',message='Version installée à jour.',latest=tag)
        else: UPDATE.update(status='available',message='Une nouvelle version stable est disponible.',release=release_info(data),latest=tag)
    except Exception as e:
        logging.info('Vérification GitHub indisponible : %s',e)
        UPDATE.update(status='unavailable',message='Vérification indisponible (réseau, Release absente ou distribution incomplète). La comptabilité reste utilisable.',detail=str(e))
    finally: UPDATE_LOCK.release()


def file_hash(path):
    h=hashlib.sha256()
    with open(path,'rb') as f:
        for chunk in iter(lambda:f.read(1024*1024),b''): h.update(chunk)
    return h.hexdigest()


def bundle_binary(path):
    return path/'Contents/MacOS/MMA Comptabilité' if path.suffix=='.app' else path


def install_update():
    if not UPDATE_LOCK.acquire(False): return
    try:
        release=UPDATE.get('release')
        if not release or version_tuple(release['version'])<=version_tuple(APP_VERSION): raise ValueError('Aucune mise à jour plus récente prête.')
        UPDATE.update(status='installing',message='Téléchargement et vérification…')
        frozen=getattr(sys,'frozen',False)
        target=Path(sys.executable if frozen else __file__).resolve()
        if frozen and sys.platform=='darwin':
            target=next((p for p in target.parents if p.suffix=='.app'),None)
            if not target: raise ValueError('Bundle macOS introuvable.')
        stage=Path(tempfile.mkdtemp(prefix='.mma-update-',dir=target.parent))
        download=stage/'download'
        size=github_download(release['url'],400*1024*1024,download)
        if size!=release['size'] or file_hash(download)!=release['digest']: raise ValueError('Empreinte ou taille incorrecte. Installation annulée.')
        candidate=stage/target.name
        if target.suffix=='.app':
            with zipfile.ZipFile(download) as z:
                if sum(x.file_size for x in z.infolist())>1500*1024*1024: raise ValueError('Archive trop volumineuse.')
                for item in z.infolist():
                    parts=Path(item.filename).parts
                    if not parts or parts[0]!=target.name or '..' in parts or Path(item.filename).is_absolute() or '\\' in item.filename: raise ValueError('Chemin d’archive interdit.')
                    if (item.external_attr>>16)&0o170000==0o120000:
                        link=z.read(item).decode()
                        dest=(stage/item.filename).parent/link
                        if not dest.resolve().is_relative_to(candidate.resolve()): raise ValueError('Lien sortant du bundle interdit.')
            subprocess.run(['/usr/bin/ditto','-x','-k',str(download),str(stage)],check=True)
            if not bundle_binary(candidate).is_file(): raise ValueError('Bundle incomplet.')
        else:
            if frozen and download.read_bytes()[:2]!=b'MZ': raise ValueError('Exécutable Windows invalide.')
            if not frozen:
                tree=ast.parse(download.read_text(encoding='utf-8'))
                versions=[ast.literal_eval(n.value) for n in tree.body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='APP_VERSION' for t in n.targets)]
                if versions!=[release['version']]: raise ValueError('Version du script incohérente.')
            os.replace(download,candidate)
        STORE.backup('avant-mise-a-jour')
        helper=stage/('helper.app' if target.suffix=='.app' else 'helper'+target.suffix)
        if target.is_dir(): shutil.copytree(target,helper,symlinks=True)
        else: shutil.copy2(target,helper)
        plan={'target':str(target),'candidate':str(candidate),'old_hash':file_hash(bundle_binary(target)),
              'new_hash':file_hash(bundle_binary(candidate)),'version':release['version'],'data_dir':str(STORE.folder),
              'nonce':secrets.token_hex(24),'pid':os.getpid(),'source':not frozen}
        plan_file=stage/'plan.json'; plan_file.write_text(json.dumps(plan),encoding='utf-8')
        command=([sys.executable,str(helper)] if not frozen else [str(bundle_binary(helper))])+['--apply-update',str(plan_file)]
        env={**os.environ,'PYINSTALLER_RESET_ENVIRONMENT':'1'}
        options={'creationflags':subprocess.CREATE_NO_WINDOW} if os.name=='nt' else {'start_new_session':True}
        subprocess.Popen(command,env=env,stdin=subprocess.DEVNULL,stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL,**options)
        UPDATE.update(status='staged',message='Mise à jour vérifiée. Fermeture et redémarrage…')
        if WINDOW:
            READY.set(); WINDOW.destroy()
    except Exception as e:
        logging.exception('Mise à jour annulée')
        UPDATE.update(status='error',message=str(e))
    finally: UPDATE_LOCK.release()


def apply_update(plan_path):
    """Helper indépendant : remplacement après libération du verrou, rollback programme."""
    plan_path=Path(plan_path).resolve(); stage=plan_path.parent
    p=json.loads(plan_path.read_text(encoding='utf-8'))
    target=Path(p['target']).resolve(); candidate=Path(p['candidate']).resolve()
    if not stage.name.startswith('.mma-update-') or target.parent!=stage.parent or candidate.parent!=stage or candidate.name!=target.name or target.suffix not in ('.py','.exe','.app'):
        raise ValueError('Plan de mise à jour invalide.')
    if target.name in ('Data.db','Dominis.py'): raise ValueError('Cible protégée.')
    previous=stage/('previous'+target.suffix)
    # Le verrou ne peut être libéré qu’après la fermeture du serveur et de SQLite.
    guard=None
    for _ in range(600):
        try: guard=InstanceGuard(Path(p['data_dir'])); break
        except OSError: time.sleep(.1)
    if guard is None: raise TimeoutError('L’ancienne application est encore ouverte.')
    child=None; replaced=False
    log=stage/'update.log'
    try:
        if file_hash(bundle_binary(target))!=p['old_hash'] or file_hash(bundle_binary(candidate))!=p['new_hash']: raise ValueError('Programme modifié pendant la mise à jour.')
        os.replace(target,previous)
        try: os.replace(candidate,target)
        except Exception: os.replace(previous,target); raise
        replaced=True
        guard.close(); guard=None
        ready=stage/'ready.json'
        command=([sys.executable,str(target)] if p['source'] else [str(bundle_binary(target))])+['--data-dir',p['data_dir'],'--update-ready',str(ready),'--update-nonce',p['nonce']]
        env={**os.environ,'PYINSTALLER_RESET_ENVIRONMENT':'1'}
        child=subprocess.Popen(command,env=env)
        deadline=time.monotonic()+90
        while time.monotonic()<deadline:
            if child.poll() is not None: raise RuntimeError('Nouvelle version arrêtée au démarrage.')
            if ready.exists() and json.loads(ready.read_text())=={'version':p['version'],'nonce':p['nonce']}:
                log.write_text('Mise à jour confirmée. Ancienne version conservée dans '+str(previous),encoding='utf-8'); return 0
            time.sleep(.2)
        raise TimeoutError('Démarrage non confirmé.')
    except Exception as e:
        if child and child.poll() is None:
            child.terminate()
            try: child.wait(10)
            except subprocess.TimeoutExpired: child.kill(); child.wait()
        if replaced:
            os.replace(target,stage/('failed'+target.suffix)); os.replace(previous,target)
        log.write_text('Échec ; programme précédent rétabli. '+str(e),encoding='utf-8')
        if guard: guard.close(); guard=None
        if replaced:
            cmd=([sys.executable,str(target)] if p['source'] else [str(bundle_binary(target))])+['--data-dir',p['data_dir'],'--no-update']
            subprocess.Popen(cmd,env={**os.environ,'PYINSTALLER_RESET_ENVIRONMENT':'1'})
        return 1
    finally:
        if guard: guard.close()


def export_data(fmt, filters=None):
    s=STORE.state(); filters=filters or {}
    entries=s['entries']
    if filters.get('period'):
        period=next((p for p in s['periods'] if p['id']==filters['period']),None)
        if not period: raise ValueError('Exercice introuvable.')
        entries=[e for e in entries if period['start']<=e['date']<=period['end']]
    if filters.get('account'): entries=[e for e in entries if filters['account'] in (e['account_id'],e['target_id'])]
    entries=sorted(entries,key=lambda e:(e['date'],e['created']))
    accounts={a['id']:a['name'] for a in s['accounts']}; cats={c['id']:c['name'] for c in s['categories']}
    rows=[['Date','Libellé','Sens','Montant','Compte','Destination','Catégorie','Paiement','Référence','Pointée','Notes']]
    rows += [[e['date'],e['label'],e['direction'],euro(e['amount']),accounts.get(e['account_id'],''),accounts.get(e['target_id'],''),cats.get(e['category_id'],''),e['payment'],e['reference'],'Oui' if e['cleared'] else 'Non',e['notes']] for e in entries]
    if fmt=='json':
        return json.dumps({'application':APP_NAME,'version':1,'exported_at':now(),'entries':[{**e,'category':cats.get(e['category_id'],''),'account':accounts.get(e['account_id'],''),'target_account':accounts.get(e['target_id'],'')} for e in entries]},ensure_ascii=False).encode(), 'application/json','mouvements.json'
    if fmt=='csv':
        output=io.StringIO(); writer=csv.writer(output,delimiter=';')
        for i,row in enumerate(rows):
            converted=list(row)
            if i: converted[3]=converted[3].replace('.',',')
            writer.writerow(["'"+v if isinstance(v,str) and v.startswith(('=','+','-','@','\t','\r')) else v for v in converted])
        return output.getvalue().encode('utf-8-sig'),'text/csv','mouvements.csv'
    if fmt=='xlsx':
        from openpyxl import Workbook
        from openpyxl.styles import Font, PatternFill
        book=Workbook(); sheet=book.active; sheet.title='Mouvements'
        for row in rows:
            sheet.append(row)
            for cell in sheet[sheet.max_row]:
                if isinstance(cell.value,str): cell.data_type='s'
            if sheet.max_row>1:
                cell=sheet.cell(sheet.max_row,4)
                cell.value=Decimal(row[3]);cell.number_format='#,##0.00'
        for cell in sheet[1]: cell.font=Font(bold=True,color='FFFFFF'); cell.fill=PatternFill('solid',fgColor='B91C2B')
        for column,width in {'A':14,'B':42,'C':14,'D':16,'E':24,'F':24,'G':26,'H':18,'I':24,'J':12,'K':50}.items(): sheet.column_dimensions[column].width=width
        sheet.freeze_panes='A2'; sheet.auto_filter.ref=sheet.dimensions
        output=io.BytesIO(); book.save(output)
        return output.getvalue(),'application/vnd.openxmlformats-officedocument.spreadsheetml.sheet','mouvements.xlsx'
    if fmt=='pdf':
        income=sum(e['amount'] for e in entries if e['direction']=='Recette'); expense=sum(e['amount'] for e in entries if e['direction']=='Dépense')
        model={'title':s['settings']['owner'],'eyebrow':'MMA COMPTABILITÉ · SYNTHÈSE DE TRÉSORERIE',
               'subtitle': 'Exercice sélectionné' if filters.get('period') else 'Toutes les périodes',
               'meta':['Édité le '+dt.date.today().isoformat(),str(len(entries))+' opérations'],
               'notice':'Synthèse des flux enregistrés, hors virements internes. Ne constitue pas un bilan en partie double ni une attestation de conformité.',
               'sections':[{'title':'Recettes et dépenses','table':{'headers':['Recettes','Dépenses','Solde des flux'],'rows':[[euro(income)+' €',euro(expense)+' €',euro(income-expense)+' €']]}},
                           {'title':'Journal des mouvements','table':{'headers':['Date','Libellé','Sens','Montant €','Compte'],'weights':[1,2.5,1,1,1.5],'rows':[[r[0],r[1],r[2],r[3],r[4]] for r in rows[1:]]}}],
               'footer':'MMA Fight Club Calais · Données locales · '+APP_VERSION}
        doc=PdfAnnualReport(model); doc.render(); data,_=doc.build()
        return data,'application/pdf','synthese.pdf'
    if fmt=='audit':
        with STORE.db() as c: data=[dict(r) for r in c.execute('SELECT * FROM audit ORDER BY id')]
        return json.dumps(data,ensure_ascii=False,indent=2).encode(),'application/json','historique.json'
    raise ValueError('Format inconnu.')


def native_save(raw,name):
    if not WINDOW: return {'blob':base64.b64encode(raw).decode(),'filename':name}
    import webview
    result=WINDOW.create_file_dialog(webview.FileDialog.SAVE,save_filename=name)
    if not result: return {'cancelled':True}
    target=Path(result[0] if isinstance(result,(list,tuple)) else result).resolve()
    if target==STORE.path or target.is_relative_to(STORE.backups) or target.suffix.lower() in ('.py','.exe','.app'):
        raise ValueError('Choisissez un emplacement d’export distinct des données et du programme.')
    fd,temp=tempfile.mkstemp(dir=target.parent,prefix='.mma-export-'); os.close(fd)
    try:
        Path(temp).write_bytes(raw)
        with open(temp,'rb+') as f: os.fsync(f.fileno())
        os.replace(temp,target)
    finally: Path(temp).unlink(missing_ok=True)
    return {'saved':str(target)}


class Handler(BaseHTTPRequestHandler):
    def log_message(self,*args): pass
    def reply(self,data,status=200,mime='application/json; charset=utf-8',extra=None):
        raw=data if isinstance(data,bytes) else data.encode() if isinstance(data,str) else json.dumps(data,ensure_ascii=False).encode()
        self.send_response(status)
        for k,v in {'Content-Type':mime,'Content-Length':str(len(raw)),'Cache-Control':'no-store','X-Content-Type-Options':'nosniff','Referrer-Policy':'no-referrer','X-Frame-Options':'SAMEORIGIN',**(extra or {})}.items(): self.send_header(k,v)
        self.end_headers()
        try: self.wfile.write(raw)
        except (BrokenPipeError,ConnectionResetError,ConnectionAbortedError): pass
    def authorized(self):
        expected=f'127.0.0.1:{self.server.server_port}'
        if self.headers.get('Host')!=expected: return False
        origin=self.headers.get('Origin')
        if origin and origin!='http://'+expected: return False
        token=self.headers.get('X-MMA-Token') or parse_qs(urlparse(self.path).query).get('token',[''])[0]
        return secrets.compare_digest(token,TOKEN)
    def do_GET(self):
        path=urlparse(self.path).path; query=parse_qs(urlparse(self.path).query)
        if not self.authorized(): return self.reply({'error':'Session locale invalide.'},403)
        try:
            if path=='/': return self.reply(HTML.replace('__TOKEN__',TOKEN),mime='text/html; charset=utf-8',extra={'Content-Security-Policy':"default-src 'self'; script-src 'self' 'unsafe-inline'; style-src 'self' 'unsafe-inline'; img-src 'self' data: blob:; frame-src 'self' blob:; object-src 'none'; connect-src 'self'; base-uri 'none'; form-action 'none'; frame-ancestors 'self'"})
            if path=='/logo.png': return self.reply(LOGO_PNG,mime='image/png')
            if path=='/api/state': return self.reply(STORE.state())
            if path=='/api/update': return self.reply(UPDATE)
            if path=='/api/document':
                with LOCK,STORE.db() as c: d=c.execute('SELECT * FROM documents WHERE id=?',(query.get('id',[''])[0],)).fetchone()
                if not d: raise ValueError('Document introuvable.')
                raw=d['data']; ext=Path(d['filename']).suffix.lower()
                if query.get('preview')==['1']:
                    if ext=='.docx':
                        safe_zip(raw)
                        with zipfile.ZipFile(io.BytesIO(raw)) as z: tree=ET.fromstring(z.read('word/document.xml'))
                        return self.reply({'type':'text','text':'\n'.join(''.join(t.text or '' for t in e.iter() if t.tag.endswith('}t')) for e in tree.iter() if e.tag.endswith('}p'))})
                    if ext=='.xlsx':
                        safe_zip(raw)
                        from openpyxl import load_workbook
                        b=load_workbook(io.BytesIO(raw),read_only=True,data_only=True)
                        try: return self.reply({'type':'text','text':'\n\n'.join(name+'\n'+'\n'.join(' | '.join(str(v or '') for v in r) for r in list(b[name].iter_rows(max_row=200,max_col=25,values_only=True))) for name in b.sheetnames[:10])})
                        finally: b.close()
                    if ext in ('.txt','.csv','.tsv','.json','.md','.xml','.html'): return self.reply({'type':'text','text':decode_text(raw)[:200000]})
                    return self.reply({'type':'pdf' if raw.startswith(b'%PDF') else 'image' if ext in ('.png','.jpg','.jpeg','.gif','.webp','.bmp') else 'binary'})
                safe_types={'.png':'image/png','.jpg':'image/jpeg','.jpeg':'image/jpeg','.gif':'image/gif','.webp':'image/webp','.bmp':'image/bmp','.pdf':'application/pdf'}
                mime=safe_types.get(ext,'application/octet-stream')
                return self.reply(raw,mime=mime,extra={'Content-Security-Policy':"sandbox; default-src 'none'",'Content-Disposition':('inline' if ext in safe_types else 'attachment')+"; filename*=UTF-8''"+quote(d['filename'])})
            return self.reply({'error':'Ressource introuvable.'},404)
        except Exception as e: logging.exception('Lecture'); return self.reply({'error':str(e)},400)
    def do_POST(self):
        if not self.authorized(): return self.reply({'error':'Session locale invalide.'},403)
        try:
            size=int(self.headers.get('Content-Length','0'))
            if not 0<size<=700*1024*1024: raise ValueError('Requête trop volumineuse ou vide.')
            self.connection.settimeout(60)
            p=json.loads(self.rfile.read(size))
            if not isinstance(p,dict): raise ValueError('Requête invalide.')
            action=urlparse(self.path).path.removeprefix('/api/')
            if action=='import-preview': result=preview_import(p)
            elif action=='import': result=commit_import(p)
            elif action=='recurrence-preview': result=recurrence_preview(p)
            elif action=='backup':
                target=STORE.backup(); result=native_save(target.read_bytes(),target.name) if p.get('export') else {'name':target.name}
            elif action=='restore':
                if p.get('name'):
                    path=STORE.backups/Path(p['name']).name
                    if path.parent!=STORE.backups or not path.is_file(): raise ValueError('Sauvegarde introuvable.')
                    raw=path.read_bytes()
                else: raw=decode_file(p.get('blob',''),500*1024*1024)
                STORE.restore(raw,p.get('confirmation')); result={'ok':True}
            elif action=='export':
                raw,_,name=export_data(p.get('format'),p); result=native_save(raw,name)
            elif action=='document-export':
                with LOCK,STORE.db() as c: d=c.execute('SELECT * FROM documents WHERE id=?',(p.get('id'),)).fetchone()
                if not d: raise ValueError('Document introuvable.')
                result=native_save(d['data'],d['filename'])
            elif action=='check-update': threading.Thread(target=check_updates,daemon=True).start(); result={'ok':True}
            elif action=='install-update':
                if p.get('confirmation')!='INSTALLER': raise ValueError('Confirmation requise.')
                threading.Thread(target=install_update,daemon=True).start(); result={'ok':True}
            elif action=='integrity':
                with LOCK,STORE.db() as c: STORE.validate(c)
                result={'ok':True}
            else: result=STORE.mutate(action,p)
            self.reply(result)
        except Exception as e:
            logging.exception('Action refusée')
            self.reply({'error':str(e)},400)


def backup_loop():
    while not STOP.wait(15*60):
        try: STORE.backup('auto')
        except Exception as e: STORE.backup_error=str(e); logging.exception('Sauvegarde automatique')


def on_closing():
    if READY.is_set(): return True
    if UPDATE_LOCK.locked() and UPDATE.get('status')=='installing': return False
    if not CLOSE_LOCK.acquire(False): return False
    def close_worker():
        try:
            answer=[]; event=threading.Event()
            WINDOW.evaluate_js('Promise.resolve(window.mmaCanClose ? window.mmaCanClose() : true)',callback=lambda value:(answer.append(value),event.set()))
            if not event.wait(30) or answer[0] is not True: return
            if not STORE.recovery: STORE.backup('fermeture')
            READY.set(); WINDOW.destroy()
        except Exception as e:
            STORE.backup_error=str(e)
            WINDOW.evaluate_js('alert('+json.dumps('Fermeture annulée : sauvegarde impossible. '+str(e))+')')
        finally: CLOSE_LOCK.release()
    threading.Thread(target=close_worker,daemon=True).start()
    return False


HTML = r'''<!doctype html><html lang="fr"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>MMA Comptabilité</title><style>
__CSS__
:root{--bg:#111113;--side:#151517;--panel:#1b1b1e;--panel2:#232326;--line:#303034;--text:#f4f3f4;--muted:#a0a0aa;--gold:#ef5363;--goldbg:#382025;--green:#87c9a4;--red:#ff8791;--blue:#96adeb}
:root[data-theme=light]{--bg:#f4f4f6;--side:#fff;--panel:#fff;--panel2:#f1f1f4;--line:#dddde3;--text:#24242b;--muted:#656570;--gold:#bb2038;--goldbg:#fbe9ed;--green:#26744b;--red:#bf253b;--blue:#385eae}
button.primary{background:#c92940;border-color:#c92940;color:#fff}.brand{height:118px;padding:20px 17px}.brand-mark{width:56px;height:56px;border-radius:0}.brand-name{font-size:21px;letter-spacing:.3px}.brand-caption{font-size:8px;letter-spacing:.6px;white-space:normal}.charts-grid>.panel{margin-top:0}.workspace{margin-bottom:22px}.page-head h1{font-size:34px}.hero-note{font-size:12px;color:var(--muted);margin-top:8px}.panel+.panel{margin-top:18px}.panel-body>.row{margin-bottom:12px}.filters{flex-wrap:wrap}.filters input[type=search]{flex:1;min-width:180px}.filters select{max-width:190px}.cell-label{white-space:normal;min-width:160px;max-width:280px}.form-grid{gap:15px}.form-grid .full{grid-column:1/-1}.field small{color:var(--muted)}.modal.wide{width:1060px}#modal-form{display:flex;flex-direction:column;min-height:0;overflow:hidden}.modal-content{min-height:0;overflow:auto}.modal-head,.modal-footer{flex-shrink:0}.modal table input{min-width:100px;padding:7px}.modal table select{min-width:145px;padding:7px}.modal table td{padding:7px}.modal table input[type=checkbox]{min-width:15px}.modal .notice{white-space:pre-wrap}.error:empty{display:none}.empty{min-height:160px}.audit-detail{white-space:pre-wrap;word-break:break-word;max-width:650px;font-size:11px}.bar-chart{display:flex;align-items:end;gap:12px;height:205px;padding:22px 8px 0}.month-bars{flex:1;height:100%;display:flex;align-items:end;justify-content:center;gap:3px;position:relative;padding-bottom:24px}.month-bars i{width:35%;min-height:1px;border-radius:3px 3px 0 0}.month-bars span{position:absolute;bottom:0;color:var(--muted);font-size:9px}.budget-track{height:7px;background:var(--line);border-radius:5px;overflow:hidden;min-width:100px}.budget-track i{display:block;height:100%;background:var(--gold)}.month-total-row td{background:var(--panel2);font-weight:600}.pager{padding:15px;display:flex;justify-content:space-between;align-items:center;gap:10px}.doc-viewport{height:60vh;overflow:auto;background:var(--bg);border:1px solid var(--line);border-radius:8px;padding:12px}.doc-viewport iframe{width:100%;height:100%;border:0;background:white}.doc-viewport img{display:block;max-width:none;transform-origin:top left}.doc-viewport pre{white-space:pre-wrap;overflow-wrap:anywhere;margin:0}.status-line{font-size:11px;color:var(--muted);margin-top:10px}.compact td{padding:8px 14px}.compact th{padding:9px 14px}.actions button{font-size:10px}.full-width{grid-column:1/-1}.warning{color:var(--red)}.import-error{border-left:3px solid var(--red)}.selected-total{padding:12px;background:var(--goldbg);border-radius:7px;margin:10px 0}.amount{white-space:nowrap}button:focus-visible{outline:2px solid var(--gold);outline-offset:3px}.nav-item .glyph{font-size:17px;width:20px;text-align:center}input[type=checkbox]{accent-color:#c92940}.doclist{display:grid;grid-template-columns:repeat(auto-fill,minmax(230px,1fr));gap:14px}.doccard{padding:18px;border:1px solid var(--line);border-radius:10px;background:var(--panel)}.doccard h3{overflow-wrap:anywhere}.doccard .sub{margin:8px 0 15px}.app-error{padding:50px;color:var(--red)}@media(prefers-reduced-motion:reduce){*{animation:none!important;transition:none!important}}@media(max-width:1050px){.settings-grid,.charts-grid{grid-template-columns:1fr}.kpis{grid-template-columns:repeat(2,1fr)}#sidebar{width:210px}#shell{margin-left:210px}.brand-name{font-size:18px}}@media print{#sidebar,header,.toolbar,.filters,.actions,.footer{display:none}#shell{margin:0}main{padding:0}body{color:#111;background:#fff}}

/* Identité du club : structure Dominis, typographie de travail et accents sportifs. */
.charts-grid>.panel{margin-top:0}
body{font-family:"Segoe UI",-apple-system,BlinkMacSystemFont,Arial,sans-serif;font-size:13px}
h1,.modal-head h2{font-family:inherit;font-weight:650;letter-spacing:-1px}h1,.page-head h1{font-size:32px}.modal-head h2{font-size:22px;letter-spacing:-.5px}
.kpi-value{font-family:inherit;font-size:30px;font-weight:600;letter-spacing:-1px;font-variant-numeric:tabular-nums}.brand-name{font-family:inherit;font-weight:850;font-size:29px;font-style:italic;letter-spacing:-1px}.brand-caption{font-weight:650;letter-spacing:1px}.brand{position:relative}.brand:after{content:"";position:absolute;left:18px;right:18px;bottom:8px;height:2px;background:linear-gradient(90deg,#c92940 0 30%,var(--line) 30%)}
.page-head .eyebrow{display:flex;align-items:center;gap:9px;font-size:10px;letter-spacing:1.5px}.page-head .eyebrow:before{content:"";height:12px;width:4px;background:#d62b43;transform:skew(-12deg)}
.kpi{position:relative;overflow:hidden}.kpi:before{content:"";position:absolute;left:0;top:18px;bottom:18px;width:2px;background:var(--line)}.kpi:has(.green):before{background:var(--green)}.kpi:has(.red):before{background:var(--red)}
.nav-item{font-size:12px}.nav-item .icon{width:18px;height:18px}.month-bars{max-width:70px;min-width:35px}.bar-chart{justify-content:space-around}.month-bars i{max-width:25px}.kpi-top{min-height:17px}.kpi-bottom{line-height:1.5}td{font-size:12px}td strong{font-size:12px}th{font-size:10px}.modal-footer{background:var(--panel2)}.primary{box-shadow:0 3px 10px #b91c2b18}.nav-item:focus-visible{outline:2px solid var(--gold);outline-offset:-2px}
header .save-state{color:var(--muted);font-size:10px;display:inline-flex;align-items:center;gap:7px}.save-state:before{content:"";width:6px;height:6px;border-radius:50%;background:var(--green)}.save-state[data-busy=true]:before{background:var(--gold)}
:root[data-motion=off] *{animation:none!important;transition:none!important}
@media(prefers-reduced-motion:no-preference){:root:not([data-motion=off]) button{transition:background-color .15s,border-color .15s,box-shadow .15s,transform .15s}:root:not([data-motion=off]) button:active{transform:translateY(1px)}:root:not([data-motion=off]) .nav-item:hover .icon{transform:translateX(2px)}:root:not([data-motion=off]) .nav-item .icon{transition:transform .18s}:root:not([data-motion=off]) .doccard{transition:border-color .18s,transform .18s}:root:not([data-motion=off]) .doccard:hover{border-color:var(--gold);transform:translateY(-2px)}}
@media(max-width:1100px){header .save-state{display:none}}

</style></head><body>
<aside id="sidebar"><div class="brand"><img class="brand-mark" src="/logo.png?token=__TOKEN__" alt="Logo MMA Fight Club Calais"><div><div class="brand-name">MMA</div><div class="brand-caption">Comptabilité du club</div></div></div><div class="workspace"><span class="status-dot"></span><div><strong>MMA Fight Club Calais</strong><div class="sub">Votre espace comptable</div></div></div><nav class="nav-scroll" id="nav" aria-label="Navigation principale"></nav><div class="nav-bottom"><button class="nav-item" data-page="settings"><span class="glyph">⚙</span>Paramètres & sauvegardes</button><div class="local-status"><span class="status-dot"></span>Données locales · SQLite</div></div></aside>
<div id="shell"><header><div class="breadcrumb">MMA Fight Club Calais <span aria-hidden="true"> / </span><b id="crumb">Vue d’ensemble</b></div><div class="row"><span class="save-state" id="save-state" role="status">Données enregistrées</span><span class="top-date" id="today"></span><button data-action="theme" aria-label="Changer de thème">◐</button><button class="primary" data-action="new-entry">+ Opération</button></div></header><main id="main"><div class="loading">Ouverture de votre comptabilité…</div></main></div><div id="modal"></div><div id="toasts" class="toast-container" role="status" aria-live="polite"></div>
<script>
'use strict';
const TOKEN='__TOKEN__';
const $=(q,r=document)=>r.querySelector(q),$$=(q,r=document)=>[...r.querySelectorAll(q)];
const esc=v=>String(v??'').replace(/[&<>"']/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
const money=c=>new Intl.NumberFormat('fr-FR',{style:'currency',currency:'EUR'}).format(c/100);
const amount=c=>(c/100).toFixed(2);
const today=()=>{let d=new Date();return d.getFullYear()+'-'+String(d.getMonth()+1).padStart(2,'0')+'-'+String(d.getDate()).padStart(2,'0')};
const date=v=>v?String(v).split('-').reverse().join('/'):'—';
const paths={grid:'M3 3h7v7H3z M14 3h7v7h-7z M3 14h7v7H3z M14 14h7v7h-7z',building:'M4 21V7l8-4 8 4v14 M2 21h20 M8 8v2 M12 7v3 M16 8v2 M8 13v2 M12 13v2 M16 13v2 M10 21v-3h4v3',wallet:'M3 6h16v14H3z M3 6V4h14v2 M15 11h6v5h-6z M17 13.5h1',calendar:'M4 5h16v16H4z M8 3v4 M16 3v4 M4 10h16 M8 14h2 M14 14h2 M8 17h2',folder:'M3 6h7l2 2h9v12H3z',settings:'M9 3h6l1 3 3 1 2 5-2 5-3 1-1 3H9l-1-3-3-1-2-5 2-5 3-1z M15 12a3 3 0 1 1-6 0 3 3 0 0 1 6 0',exit:'M10 4H4v16h6 M13 8l4 4-4 4 M8 12h13',chevron:'m9 5 7 7-7 7',down:'m6 9 6 6 6-6',up:'m6 15 6-6 6 6',arrow:'M5 12h14 m-5-5 5 5-5 5',plus:'M12 5v14 M5 12h14',search:'M16 16l5 5 M18 10a8 8 0 1 1-16 0 8 8 0 0 1 16 0',panel:'M3 4h18v16H3z M9 4v16',bell:'M6 8a6 6 0 0 1 12 0v7l3 3H3l3-3z M10 21h4',download:'M12 3v12 m-5-5 5 5 5-5 M4 16v5h16v-5',upload:'M12 16V4 m-5 5 5-5 5 5 M4 17v4h16v-4',trend:'m3 17 6-6 4 3 8-10 M15 4h6v6',check:'m5 12 4 4L19 6',close:'m6 6 12 12 M6 18 18 6',edit:'m14 5 5 5 M4 20l5-1L21 7l-5-5L4 14z',trash:'M4 6h16 M9 6V3h6v3 M6 6l1 15h10l1-15 M10 10v7 M14 10v7',users:'M16 21v-3c0-4-12-4-12 0v3 M10 3a4 4 0 1 1 0 8 4 4 0 0 1 0-8 M17 4a4 4 0 0 1 0 7 M18 15c3 0 4 1 4 4v2',file:'M5 3h9l5 5v13H5z M14 3v6h5 M8 13h8 M8 17h6',lock:'M5 10h14v11H5z M8 10V6a4 4 0 0 1 8 0v4 M12 14v3',sun:'M12 2v2 M12 20v2 M2 12h2 M20 12h2 M5 5l1 1 M18 18l1 1 M5 19l1-1 M18 6l1-1 M17 12a5 5 0 1 1-10 0 5 5 0 0 1 10 0',moon:'M21 13A9 9 0 0 1 11 3a9 9 0 1 0 10 10',database:'M3 6c0-5 18-5 18 0s-18 5-18 0 M3 6v12c0 5 18 5 18 0V6 M3 12c0 5 18 5 18 0',info:'M12 11v6 M12 7v1 M22 12a10 10 0 1 1-20 0 10 10 0 0 1 20 0',home:'m3 10 9-7 9 7 M5 9v12h14V9 M9 21v-7h6v7',more:'M5 12h1 M11 12h1 M17 12h1',clock:'M12 6v6l4 2 M22 12a10 10 0 1 1-20 0 10 10 0 0 1 20 0',refresh:'M20.5 12a8.5 8.5 0 1 1-2.6-6.1 M20.5 3.5v5h-5',percent:'m5 19 14-14 M9 6a3 3 0 1 1-6 0 3 3 0 0 1 6 0 M21 18a3 3 0 1 1-6 0 3 3 0 0 1 6 0',print:'M7 8V3h10v5 M7 17H3V8h18v9h-4 M7 14h10v7H7z'};
const icon=n=>`<svg class="icon" viewBox="0 0 24 24" aria-hidden="true"><path d="${paths[n]||paths.file}"/></svg>`;
const navIcons={dashboard:'grid',journal:'file',accounts:'wallet',budgets:'percent',reports:'trend',documents:'folder',periods:'calendar',categories:'grid',audit:'clock',settings:'settings'};
const pages={dashboard:['Vue d’ensemble','◈'],journal:['Journal des opérations','≡'],accounts:['Comptes & rapprochement','▣'],budgets:['Budgets','▥'],reports:['Synthèses','↗'],documents:['Justificatifs','▤'],periods:['Exercices','□'],categories:['Catégories','◇'],audit:['Historique','◷'],settings:['Paramètres & sauvegardes','⚙']};
window.S=null;let page='dashboard',period='',account='',direction='',query='',pageNumber=0,dirty=false,modalSave=null,lastFocus=null,importRows=[],previewWarnings=[],updateDismissed='';let renderedPage=null;let activeMotion=[];const motionMedia=matchMedia('(prefers-reduced-motion: reduce)');
const motionEnabled=()=>!motionMedia.matches&&S?.settings.motion!=='off';
function cancelMotion(){activeMotion.forEach(a=>a.cancel());activeMotion=[]}
motionMedia.addEventListener?.('change',()=>{if(!motionEnabled())cancelMotion()});
function animatePage(){cancelMotion();if(!motionEnabled())return;let els=$$('.page-head,.kpis,.charts-grid,.settings-grid,.doclist,#main>section');els.slice(0,5).forEach((el,i)=>{let animation=el.animate([{opacity:.35,transform:'translateY(7px)'},{opacity:1,transform:'translateY(0)'}],{duration:220,delay:Math.min(i*25,75),easing:'cubic-bezier(.2,.8,.2,1)'});activeMotion.push(animation)})}

async function api(action,data){let r=await fetch('/api/'+action,{method:data===undefined?'GET':'POST',headers:{'X-MMA-Token':TOKEN,'Content-Type':'application/json'},body:data===undefined?undefined:JSON.stringify(data)});let v=await r.json();if(!r.ok)throw Error(v.error||'Erreur de communication');return v}
function notify(message,error=false){let el=document.createElement('div');el.className='toast'+(error?' error-toast':'');el.textContent=message;$('#toasts').append(el);setTimeout(()=>el.remove(),7000)}
async function load(){window.S=await api('state');if(!period){let p=S.periods.find(x=>x.start<=today()&&x.end>=today());period=p?.id||'all'}document.documentElement.dataset.theme=S.settings.theme;document.documentElement.dataset.motion=S.settings.motion||'auto';document.body.classList.toggle('compact',S.settings.density==='compact');render()}
const acct=id=>S.accounts.find(a=>a.id===id)?.name||'—';const cat=id=>S.categories.find(c=>c.id===id)?.name||'Virement interne';
function currentPeriod(){return S.periods.find(p=>p.id===period)}
function selectedEntries(){let p=currentPeriod();return S.entries.filter(e=>(!p||e.date>=p.start&&e.date<=p.end)&&(!account||e.account_id===account||e.target_id===account)&&(!direction||e.direction===direction)&&(!query||[e.label,e.reference,e.notes,cat(e.category_id),acct(e.account_id)].join(' ').toLocaleLowerCase('fr').includes(query.toLocaleLowerCase('fr')))).sort((a,b)=>a.date.localeCompare(b.date)||a.created.localeCompare(b.created))}
function totals(rows){let income=0,expense=0;rows.forEach(e=>{if(e.direction==='Recette')income+=e.amount;if(e.direction==='Dépense')expense+=e.amount});return {income,expense,net:income-expense}}
function balance(a,until=today(),clearedOnly=false){return (a.opening_date<=until?a.opening:0)+S.entries.filter(e=>e.date<=until&&(!clearedOnly||e.cleared)).reduce((n,e)=>n+(e.account_id===a.id?(e.direction==='Recette'?e.amount:-e.amount):e.target_id===a.id?e.amount:0),0)}
function signed(e,id=account){if(e.direction==='Virement')return id&&e.target_id===id?e.amount:-e.amount;return e.direction==='Recette'?e.amount:-e.amount}
function options(items,value,empty=''){return (empty?`<option value="">${esc(empty)}</option>`:'')+items.map(x=>{let [id,name]=Array.isArray(x)?x:[x.id,x.name];return `<option value="${esc(id)}" ${String(id)===String(value)?'selected':''}>${esc(name)}</option>`}).join('')}
function button(action,label,id='',cls=''){return `<button class="${cls}" data-action="${action}" data-id="${esc(id)}">${label}</button>`}
function head(title,subtitle,tools=''){return `<div class="page-head"><div><div class="eyebrow">MMA FIGHT CLUB CALAIS</div><h1>${title}</h1><p>${subtitle}</p></div><div class="toolbar">${tools}</div></div>`}
function periodSelect(){return `<select id="period-filter" aria-label="Exercice">${options([['all','Toutes les périodes'],...S.periods.sort((a,b)=>b.start.localeCompare(a.start)).map(p=>[p.id,p.name+(p.closed?' · clôturé':'')])],period)}</select>`}
function filters(full=false){return `<div class="filters">${periodSelect()}<select id="account-filter" aria-label="Compte">${options(S.accounts,account,'Tous les comptes')}</select>${full?`<select id="direction-filter" aria-label="Sens">${options(['Recette','Dépense','Virement'].map(x=>[x,x]),direction,'Tous les mouvements')}</select><input id="search" type="search" placeholder="Libellé, référence, catégorie…" aria-label="Rechercher une opération" value="${esc(query)}">`:''}</div>`}
function kpis(rows){let t=totals(rows),end=currentPeriod()?.end||today(),bal=S.accounts.filter(a=>!account||a.id===account).reduce((n,a)=>n+balance(a,end),0);return `<div class="kpis">${[[(end>today()?'Trésorerie projetée au ':'Trésorerie au ')+date(end),bal,'', 'Soldes initiaux inclus'],['Recettes',t.income,'green','Hors virements internes'],['Dépenses',t.expense,'red','Hors virements internes'],['Solde des flux',t.net,t.net<0?'red':'green','Sur les opérations affichées']].map(([title,value,color,note])=>`<div class="kpi"><div class="kpi-top">${title}</div><div class="kpi-value ${color}">${money(value)}</div><div class="kpi-bottom">${note}</div></div>`).join('')}</div>`}
function empty(text){return `<div class="empty"><h3>${text}</h3><p>Les données enregistrées apparaîtront ici.</p></div>`}
function render(){
 let pageChanged=renderedPage!==page;renderedPage=page;
 $('#nav').innerHTML=Object.entries(pages).filter(([k])=>k!=='settings').map(([k,[label,glyph]])=>`<button class="nav-item ${page===k?'active':''}" data-page="${k}">${icon(navIcons[k])}<span>${label}</span></button>`).join('');$('#crumb').textContent=pages[page][0];$('#today').textContent=new Date().toLocaleDateString('fr-FR',{day:'numeric',month:'long',year:'numeric'});
 let warning=(S.backup_error?`<div class="notice warning">Sauvegarde automatique en échec : ${esc(S.backup_error)}</div>`:'')+(S.recovery?'<div class="notice warning">La base principale était absente, mais des sauvegardes existent. Restaurez une copie depuis les paramètres avant de poursuivre la saisie.</div>':'');
 $('#main').innerHTML=warning+({dashboard:dashboard,journal:journal,accounts:accountsPage,budgets:budgetsPage,reports:reportsPage,documents:documentsPage,periods:periodsPage,categories:categoriesPage,audit:auditPage,settings:settingsPage}[page])()+`<footer class="footer"><span>${esc(S.settings.owner)} · Comptabilité de trésorerie</span><span>${esc(S.version)} · Enregistrement local immédiat</span></footer>`;tableSortInit(document);if(pageChanged)animatePage();
}
function dashboard(){let rows=selectedEntries();let t=totals(rows);let months={};rows.filter(e=>e.direction!=='Virement').forEach(e=>{let m=e.date.slice(0,7);months[m]??={income:0,expense:0};months[m][e.direction==='Recette'?'income':'expense']+=e.amount});let list=Object.entries(months).slice(-12),max=Math.max(1,...list.flatMap(([m,t])=>[t.income,t.expense]));let missing=rows.filter(e=>e.direction==='Dépense'&&!S.documents.some(d=>d.entry_id===e.id)).length;return head('Votre comptabilité, en clair.','Suivez les ressources du club et gardez la maîtrise de vos dépenses.',button('import','Importer'))+filters()+kpis(rows)+`<div class="charts-grid"><section class="panel"><div class="panel-head"><h2>Les flux mois par mois</h2><span class="sub"><span class="green">■ Recettes</span> &nbsp; <span class="red">■ Dépenses</span></span></div><div class="panel-body">${list.length?`<div class="bar-chart">${list.map(([m,t])=>`<div class="month-bars" title="${m} · Recettes ${money(t.income)} · Dépenses ${money(t.expense)}"><i style="height:${t.income/max*90}%;background:var(--green)"></i><i style="height:${t.expense/max*90}%;background:var(--red)"></i><span>${m.slice(5)}/${m.slice(2,4)}</span></div>`).join('')}</div>`:empty('Vos premiers mouvements donneront vie au graphique.')}</div></section><section class="panel"><div class="panel-head"><h2>Points de contrôle</h2></div><div class="panel-body stack"><div><strong>${rows.filter(e=>!e.cleared).length} opérations non pointées</strong><p class="sub">À comparer avec les relevés bancaires.</p></div><div><strong>${missing} dépenses sans justificatif lié</strong><p class="sub">Un contrôle documentaire, pas une preuve d’irrégularité.</p></div><div><strong>${S.backups.length?'Une sauvegarde est disponible':'Aucune sauvegarde disponible'}</strong><p class="sub">${esc(S.backups[0]?.name||'Créez une sauvegarde dans les paramètres.')}</p></div>${button('backup','Sauvegarder maintenant')}</div></section></div><section class="panel"><div class="panel-head"><h2>Dernières opérations</h2><button data-page="journal" class="text-link">Voir le journal →</button></div>${entryTable(rows.slice(-7).reverse(),'recent',false)}</section>`}
function entryTable(rows,key='journal',monthly=true){if(!rows.length)return empty('Aucune opération pour cette sélection.');let output='';rows.forEach((e,i)=>{output+=`<tr data-month="${e.date.slice(0,7)}"><td>${date(e.date)}</td><td class="cell-label"><strong>${esc(e.label)}</strong><span class="cell-sub">${esc(e.reference)}</span></td><td>${esc(cat(e.category_id))}</td><td>${esc(acct(e.account_id))}${e.target_id?`<span class="cell-sub">→ ${esc(acct(e.target_id))}</span>`:''}</td><td>${esc(e.direction)}</td><td class="align-right amount ${e.direction==='Virement'?'muted':e.direction==='Recette'?'green':'red'}">${e.direction==='Virement'?'↔ ':e.direction==='Recette'?'+ ':'− '}${money(e.amount)}</td><td>${e.cleared?'✓':'—'}</td><td><div class="actions">${button('edit-entry','Modifier',e.id)}${button('duplicate','Dupliquer',e.id)}${button('delete-entry','Supprimer',e.id,'danger')}</div></td></tr>`;if(monthly&&(!rows[i+1]||rows[i+1].date.slice(0,7)!==e.date.slice(0,7))){let t=totals(rows.filter(r=>r.date.slice(0,7)===e.date.slice(0,7)));output+=`<tr class="month-total-row" data-month="${e.date.slice(0,7)}"><td>${e.date.slice(0,7)}</td><td colspan="4">Flux du mois sur cette page · +${money(t.income)} / −${money(t.expense)}</td><td class="align-right">${money(t.net)}</td><td></td><td></td></tr>`}});return `<div class="table-wrap"><table data-sort-key="${key}"><thead><tr><th data-sort-column="date">Date</th><th>Libellé</th><th>Catégorie</th><th>Compte</th><th>Sens</th><th class="align-right">Montant</th><th>Pointée</th><th>Actions</th></tr></thead><tbody>${output}</tbody></table></div>`}
function journal(){let rows=selectedEntries();let total=Math.max(1,Math.ceil(rows.length/100));pageNumber=Math.min(pageNumber,total-1);return head('Journal des opérations','Chaque mouvement, sa catégorie et son justificatif.',button('import','Importer')+button('export','Exporter')+button('new-entry','+ Opération','','primary'))+filters(true)+kpis(rows)+`<section class="panel">${entryTable(rows.slice(pageNumber*100,(pageNumber+1)*100))}<div class="pager"><span class="sub">${rows.length} opérations · Page ${pageNumber+1} / ${total} · Tri sur la page affichée</span><div class="row">${button('prev','← Précédente')}${button('next','Suivante →')}</div></div></section>`}
function accountsPage(){let end=currentPeriod()?.end||today();return head('Comptes & rapprochement','Les virements internes déplacent la trésorerie sans créer de recette ou de dépense.',button('new-account','+ Compte','','primary'))+filters()+`<div class="settings-grid">${S.accounts.map(a=>`<section class="panel"><div class="panel-head"><h2>${esc(a.name)} ${a.active?'':'· archivé'}</h2>${button('edit-account','Modifier',a.id)}</div><div class="panel-body"><div class="eyebrow">Solde au ${date(end)}</div><div class="kpi-value ${balance(a,end)<0?'red':''}">${money(balance(a,end))}</div><p class="sub">Initial : ${money(a.opening)} au ${date(a.opening_date)} (avant les opérations de ce jour)</p><div class="setting-row"><div><h3>Solde des opérations pointées</h3><p>${money(balance(a,end,true))} · solde initial inclus</p></div>${button('reconcile','Comparer au relevé',a.id)}</div><div class="row">${button('account-journal','Voir les mouvements',a.id)}${button('transfer','Virement interne',a.id)}</div></div></section>`).join('')}</div>`}
function budgetsPage(){let p=currentPeriod();let rows=selectedEntries();return head('Budgets','Comparez vos prévisions aux recettes et dépenses enregistrées.',button('new-budget','+ Prévision','','primary'))+filters()+(!p?'<div class="notice">Choisissez un exercice pour suivre son budget.</div>':`<section class="panel"><div class="table-wrap"><table data-sort-key="budgets"><thead><tr><th>Catégorie</th><th>Sens</th><th>Prévision</th><th>Réalisé</th><th>Écart réalisé − prévu</th><th>Avancement</th><th>Actions</th></tr></thead><tbody>${S.budgets.filter(b=>b.period_id===p.id).map(b=>{let realized=rows.filter(e=>e.category_id===b.category_id).reduce((n,e)=>n+e.amount,0);let c=S.categories.find(c=>c.id===b.category_id);return `<tr><td>${esc(c.name)}</td><td>${c.direction}</td><td>${money(b.amount)}</td><td>${money(realized)}</td><td class="${c.direction==='Dépense'&&realized>b.amount?'red':''}">${money(realized-b.amount)}</td><td><div class="budget-track"><i style="width:${b.amount?Math.min(100,realized/b.amount*100):0}%"></i></div></td><td>${button('edit-budget','Modifier',b.id)}</td></tr>`}).join('')||'<tr><td colspan="7">Aucun budget saisi pour cet exercice.</td></tr>'}</tbody></table></div></section>`)}
function reportsPage(){let rows=selectedEntries();return head('Synthèses financières','Comptabilité de trésorerie : flux enregistrés, sans bilan en partie double.',button('pdf','Rapport PDF')+button('export','Exporter'))+filters()+kpis(rows)+`<section class="panel"><div class="panel-head"><h2>Répartition par catégorie</h2></div><div class="table-wrap"><table data-sort-key="report"><thead><tr><th>Catégorie</th><th>Sens</th><th>Nombre</th><th>Total</th></tr></thead><tbody>${S.categories.map(c=>{let es=rows.filter(e=>e.category_id===c.id);return es.length?`<tr><td>${esc(c.name)}</td><td>${c.direction}</td><td>${es.length}</td><td class="${c.direction==='Recette'?'green':'red'}">${money(es.reduce((n,e)=>n+e.amount,0))}</td></tr>`:''}).join('')||'<tr><td colspan="4">Aucun mouvement.</td></tr>'}</tbody></table></div></section><p class="hero-note">Les soldes des comptes incluent leur historique antérieur à l’exercice. Les virements internes sont exclus des flux de recettes et dépenses.</p>`}
function documentsPage(){return head('Justificatifs','Factures, relevés et pièces comptables conservés dans Data.db.',button('new-document','+ Ajouter un document','','primary'))+`<div class="filters"><input id="doc-search" type="search" placeholder="Rechercher un titre ou un dossier" aria-label="Rechercher un justificatif"></div><div class="doclist">${S.documents.map(d=>`<article class="doccard" data-doc-search="${esc((d.name+' '+d.folder).toLowerCase())}"><div class="eyebrow">${esc(d.folder)}</div><h3>${esc(d.name)}</h3><p class="sub">${esc(d.filename)} · ${Math.ceil(d.size/1024)} Ko<br>${d.entry_id?'Lié à une opération':'Sans opération liée'}</p><div class="row">${button('preview-document','Consulter',d.id)}${button('document-export','Exporter',d.id)}</div></article>`).join('')||empty('Aucun justificatif.')}</div>`}
function periodsPage(){return head('Exercices comptables','La clôture verrouille les opérations. Toute réouverture est motivée et tracée.',button('new-period','+ Exercice','','primary'))+`<section class="panel"><div class="table-wrap"><table data-sort-key="periods"><thead><tr><th>Exercice</th><th>Début</th><th>Fin</th><th>État</th><th>Actions</th></tr></thead><tbody>${S.periods.map(p=>`<tr><td>${esc(p.name)}</td><td>${date(p.start)}</td><td>${date(p.end)}</td><td><span class="pill ${p.closed?'':'green'}">${p.closed?'Clôturé':'Ouvert'}</span></td><td>${button(p.closed?'reopen-period':'close-period',p.closed?'Réouvrir':'Clôturer',p.id)}</td></tr>`).join('')}</tbody></table></div></section><div class="notice" style="margin-top:18px">La clôture est un verrou de travail local, pas une certification réglementaire. Aucun mouvement n’est automatiquement généré ou supprimé.</div>`}
function categoriesPage(){return head('Catégories comptables','Un classement propre aux ressources et aux charges du club.',button('new-category','+ Catégorie','','primary'))+`<section class="panel"><div class="table-wrap"><table data-sort-key="categories"><thead><tr><th>Catégorie</th><th>Sens</th><th>État</th><th>Actions</th></tr></thead><tbody>${S.categories.map(c=>`<tr><td>${esc(c.name)}</td><td class="${c.direction==='Recette'?'green':'red'}">${c.direction}</td><td>${c.active?'Active':'Archivée'}</td><td>${button('edit-category','Modifier',c.id)}</td></tr>`).join('')}</tbody></table></div></section>`}
function auditPage(){return head('Historique des actions','200 dernières actions affichées. Export intégral disponible.',button('audit-export','Exporter l’historique'))+`<section class="panel"><div class="table-wrap"><table data-sort-key="audit"><thead><tr><th>Date</th><th>Action</th><th>Détail</th></tr></thead><tbody>${S.audit.map(a=>`<tr><td>${esc(new Date(a.at).toLocaleString('fr-FR'))}</td><td>${esc(a.action)}</td><td class="audit-detail">${esc(a.detail)}</td></tr>`).join('')}</tbody></table></div></section>`}
function settingsPage(){return head('Paramètres & sauvegardes','Protégez les données du club et retrouvez vos versions précédentes.')+`<div class="settings-grid"><section class="panel"><div class="panel-head"><h2>Votre application</h2></div><div class="panel-body"><div class="setting-row"><div><h3>${esc(S.settings.owner)}</h3><p>Nom utilisé dans les rapports.</p></div>${button('owner','Renommer')}</div><div class="setting-row"><div><h3>Affichage</h3><p>Thème ${S.settings.theme==='dark'?'sombre':'clair'} · tableaux ${S.settings.density==='compact'?'compacts':'aérés'}</p></div><div class="row">${button('theme','◐ Thème')}${button('density','Densité')}${button('motion',S.settings.motion==='off'?'Animations : arrêtées':'Animations : système')}</div></div><div class="setting-row"><div><h3>Version ${esc(S.version)}</h3><p id="update-status">Vérification au démarrage, sans bloquer la comptabilité.</p></div>${button('check-update','Rechercher')}</div><p class="sub" style="overflow-wrap:anywhere">Données : ${esc(S.data_path)}</p></div></section><section class="panel"><div class="panel-head"><h2>Sauvegardes complètes</h2></div><div class="panel-body stack"><p>Copie au démarrage, toutes les 15 minutes et à la fermeture. Les 48 dernières copies automatiques sont conservées ; les copies manuelles et de précaution sont conservées sans purge automatique.</p><div class="row wrap">${button('backup','Sauvegarder','','primary')}${button('backup-export','Copier sur un autre support')}${button('restore-file','Restaurer un fichier')}</div><p class="sub">Une copie sur le même disque ne protège pas d’une panne de ce disque. Exportez régulièrement sur un support externe.</p>${button('integrity','Vérifier l’intégrité')}</div></section><section class="panel full-width"><div class="panel-head"><h2>Versions disponibles</h2><span class="sub">100 dernières copies affichées</span></div><div class="table-wrap"><table data-sort-key="backups"><thead><tr><th>Fichier daté</th><th>Taille</th><th>Actions</th></tr></thead><tbody>${S.backups.map(b=>`<tr><td>${esc(b.name)}</td><td>${Math.ceil(b.size/1024)} Ko</td><td>${button('restore-backup','Restaurer',b.name)}</td></tr>`).join('')}</tbody></table></div></section></div>`}
function field(name,label,value='',type='text',required=false,full=false,items=null){return `<div class="field ${full?'full':''}"><label for="f-${name}">${label}</label>${items?`<select id="f-${name}" name="${name}" ${required?'required':''}>${options(items,value)}</select>`:type==='textarea'?`<textarea id="f-${name}" name="${name}">${esc(value)}</textarea>`:`<input id="f-${name}" name="${name}" type="${type}" value="${esc(value)}" ${required?'required':''} ${name==='amount'||name==='opening'?'inputmode="decimal"':''}>`}</div>`}
function openModal(title,body,save=null,wide=false,label='Enregistrer'){
 if($('#modal').innerHTML&&dirty&&!confirm('Abandonner les modifications non enregistrées ?'))return false;lastFocus=document.activeElement;dirty=false;modalSave=save;
 $('#modal').innerHTML=`<div class="modal-backdrop"><section class="modal ${wide?'wide':''}" role="dialog" aria-modal="true" aria-labelledby="modal-title"><div class="modal-head"><h2 id="modal-title">${title}</h2><button data-action="close-modal" aria-label="Fermer">×</button></div><form id="modal-form"><div class="modal-content">${body}<div id="modal-error" class="error" role="alert"></div></div><div class="modal-footer"><button type="button" data-action="close-modal">${save?'Annuler':'Fermer'}</button>${save?`<button type="submit" class="primary" id="modal-submit">${label}</button>`:''}</div></form></section></div>`;
 $('#modal-form').onsubmit=async e=>{e.preventDefault();if(!modalSave)return;let b=$('#modal-submit');b.disabled=true;$('#modal-error').textContent='';try{await modalSave(Object.fromEntries(new FormData(e.target)));}catch(err){$('#modal-error').textContent=err.message}finally{if(b.isConnected)b.disabled=false}};
 setTimeout(()=>$('input,select,textarea,button',$('#modal-form'))?.focus(),0);return true;
}
function closeModal(force=false){if(!force&&dirty&&!confirm('Abandonner les modifications non enregistrées ?'))return;let root=$('#modal'),back=root.firstElementChild;const finish=()=>{if(root.firstElementChild!==back)return;root.innerHTML='';dirty=false;modalSave=null;lastFocus?.focus()};if(!force&&back&&motionEnabled()){back.inert=true;let a=back.animate([{opacity:1},{opacity:0}],{duration:120,easing:'ease-out'});a.finished.catch(()=>{}).then(finish)}else finish()}
async function saved(action,p){let status=$('#save-state');if(status){status.dataset.busy='true';status.textContent='Enregistrement…'}try{await api(action,p);closeModal(true);await load();if(status){status.dataset.busy='false';status.textContent='Données enregistrées'}notify('Enregistrement effectué.')}catch(e){if(status){status.dataset.busy='false';status.textContent='Modification non enregistrée'}throw e}}
function entryForm(e={},duplicate=false){let d={date:today(),direction:'Dépense',account_id:account||'bank',payment:'Carte',...e};if(duplicate){delete d.id;delete d.revision;d.date=''}let cats=S.categories.filter(c=>c.active&&c.direction===d.direction);let html=`<div class="form-grid">${field('date','Date',d.date,'date',true)}${field('direction','Nature',d.direction,'text',true,false,['Recette','Dépense','Virement'].map(x=>[x,x]))}${field('label','Libellé',d.label,'text',true,true)}${field('amount','Montant en euros',e.amount?amount(e.amount):'','text',true)}${field('account_id','Compte',d.account_id,'text',true,false,S.accounts.filter(a=>a.active))}${field('target_id','Compte destinataire',d.target_id,'text',false,false,[['','Choisir'],...S.accounts.filter(a=>a.active).map(a=>[a.id,a.name])])}${field('category_id','Catégorie',d.category_id,'text',false,false,[['','Choisir'],...cats.map(c=>[c.id,c.name])])}${field('payment','Moyen de paiement',d.payment,'text',true,false,['Carte','Virement','Espèces','Chèque','Prélèvement','Autre'].map(x=>[x,x]))}${field('reference','Référence',d.reference)}${field('notes','Notes',d.notes,'textarea',false,true)}${field('cleared','Pointage',d.cleared?'1':'0','text',false,false,[['0','Non pointée'],['1','Pointée sur relevé']])}</div>${d.id?`<div class="row" style="margin-top:20px">${button('attach-entry','Joindre un justificatif',d.id)}${button('recurrence','Répéter cette opération',d.id)}</div>`:''}${duplicate?'<p class="hero-note">Les champs sont recopiés ; renseignez une nouvelle date avant de confirmer.</p>':''}`;
 openModal(d.id?'Modifier l’opération':duplicate?'Dupliquer l’opération':'Nouvelle opération',html,p=>saved('entry',{...p,id:d.id,revision:d.revision}));
 const adapt=()=>{let type=$('#f-direction').value;$('#f-target_id').closest('.field').style.display=type==='Virement'?'':'none';$('#f-category_id').closest('.field').style.display=type==='Virement'?'none':'';$('#f-category_id').required=type!=='Virement';$('#f-target_id').required=type==='Virement'};
 $('#f-direction').onchange=()=>{$('#f-category_id').innerHTML=options([['','Choisir'],...S.categories.filter(c=>c.active&&c.direction===$('#f-direction').value).map(c=>[c.id,c.name])],'');adapt()};adapt();
}
function accountForm(a={}){openModal(a.id?'Modifier le compte':'Nouveau compte',`<div class="form-grid">${field('name','Nom du compte',a.name,'text',true,true)}${field('opening','Solde initial en euros',amount(a.opening||0),'text',true)}${field('opening_date','Date du solde initial',a.opening_date||today(),'date',true)}${field('active','État',a.active===0?'0':'1','text',false,false,[['1','Actif'],['0','Archivé']])}</div><p class="hero-note">Le solde initial est celui précédant les opérations de la date choisie. Il est verrouillé après la première écriture.</p>`,p=>saved('account',{...p,id:a.id}))}
function categoryForm(c={}){openModal(c.id?'Modifier la catégorie':'Nouvelle catégorie',`<div class="form-grid">${field('name','Nom',c.name,'text',true,true)}${field('direction','Sens',c.direction||'Dépense','text',true,false,[['Recette','Recette'],['Dépense','Dépense']])}${field('active','État',c.active===0?'0':'1','text',false,false,[['1','Active'],['0','Archivée']])}</div>`,p=>saved('category',{...p,id:c.id}))}
function budgetForm(b={}){openModal('Prévision budgétaire',`<div class="form-grid">${field('period_id','Exercice',b.period_id||period,'text',true,true,S.periods.filter(p=>!p.closed))}${field('category_id','Catégorie',b.category_id,'text',true,true,S.categories.filter(c=>c.active))}${field('amount','Montant prévu en euros',amount(b.amount||0),'text',true,true)}</div>`,p=>saved('budget',p))}
async function fileBase64(file){if(!file)throw Error('Choisissez un fichier.');let buf=await file.arrayBuffer();let bytes=new Uint8Array(buf),chunks=[];for(let i=0;i<bytes.length;i+=32768)chunks.push(String.fromCharCode(...bytes.subarray(i,i+32768)));return btoa(chunks.join(''))}
function documentForm(entry=''){openModal('Ajouter un justificatif',`<div class="form-grid">${field('name','Titre','','text',false,true)}${field('folder','Dossier','Justificatifs','text',true)}${field('entry_id','Opération liée',entry,'text',false,false,[['','Sans lien'],...S.entries.map(e=>[e.id,date(e.date)+' · '+e.label])])}<div class="field full"><label for="document-file">Fichier (30 Mo maximum)</label><input type="file" id="document-file" required></div></div>`,async p=>{let f=$('#document-file').files[0];if(f.size>30*1024*1024)throw Error('Maximum 30 Mo.');await saved('document',{...p,filename:f.name,blob:await fileBase64(f)})})}
async function previewDocument(id){let d=S.documents.find(d=>d.id===id);let p=await api('document?id='+encodeURIComponent(id)+'&preview=1');let url='/api/document?id='+encodeURIComponent(id)+'&token='+TOKEN;let body=p.type==='text'?`<pre id="doc-content">${esc(p.text)}</pre>`:p.type==='image'?`<img id="doc-content" src="${url}" alt="${esc(d.name)}" style="width:100%">`:p.type==='pdf'?`<iframe title="${esc(d.name)}" src="${url}"></iframe>`:'<p>Aperçu indisponible pour ce format. Exportez le fichier pour le consulter.</p>';openModal(esc(d.name),`<div class="row" style="margin-bottom:12px">${button('document-export','Exporter',id)}${p.type==='image'||p.type==='text'?'<label>Zoom <input id="doc-zoom" type="range" min="25" max="400" value="100" aria-label="Zoom du document"></label><span id="zoom-value">100 %</span>':''}</div><div class="doc-viewport">${body}</div>`,null,true);$('#doc-zoom')?.addEventListener('input',e=>{let v=e.target.value;$('#zoom-value').textContent=v+' %';if(p.type==='image')$('#doc-content').style.width=v+'%';else $('#doc-content').style.fontSize=(13*v/100)+'px'})}
async function download(action,p){let r=await api(action,p);if(r.cancelled)return;if(r.blob){let bytes=Uint8Array.from(atob(r.blob),c=>c.charCodeAt(0)),url=URL.createObjectURL(new Blob([bytes])),a=document.createElement('a');a.href=url;a.download=r.filename;a.click();setTimeout(()=>URL.revokeObjectURL(url),1000)}notify(r.saved?'Fichier enregistré : '+r.saved:'Export préparé.');return r}
function exportModal(){openModal('Exporter les mouvements',`<div class="notice">L’export reprend l’exercice et le compte sélectionnés. Les filtres de texte et de sens du journal ne limitent pas cet export. JSON contient les mouvements, la sauvegarde SQLite contient l’espace complet et ses justificatifs.</div>${field('format','Format','xlsx','text',true,true,[['xlsx','Excel XLSX'],['csv','CSV UTF-8'],['json','JSON réimportable'],['pdf','Rapport PDF']])}`,async p=>{await download('export',{...p,period:period==='all'?'':period,account});closeModal(true)},false,'Exporter')}
function confirmAction(title,message,action,data={},word='CONFIRMER',extra=''){openModal(title,`<div class="notice">${message}</div>${extra}${field('confirmation','Saisissez '+word,'','text',true,true)}`,p=>saved(action,{...data,...p}),false,'Confirmer')}
function restoreModal(name=''){openModal('Restaurer une sauvegarde',`<div class="notice">Cette action remplace tout l’espace courant, documents et paramètres compris. Une copie de précaution de la base actuelle est créée avant restauration.</div>${name?`<p>${esc(name)}</p>`:'<div class="field"><label for="restore-file">Sauvegarde SQLite</label><input type="file" id="restore-file" accept=".db" required></div>'}${field('confirmation','Saisissez RESTAURER','','text',true,true)}`,async p=>{await saved('restore',{...p,name,blob:name?undefined:await fileBase64($('#restore-file').files[0])})},false,'Restaurer')}
function importModal(){importRows=[];openModal('Importer, vérifier, confirmer',`<div class="notice">CSV, TSV, Excel XLSX, JSON MMA/Dominis, relevés PDF et TXT. Aucune écriture avant confirmation. Les doublons exacts sont ignorés.</div><div class="form-grid"><div class="field full"><label for="import-file">Fichier (30 Mo maximum)</label><input id="import-file" type="file" accept=".csv,.tsv,.xlsx,.json,.pdf,.txt" required></div>${field('account_id','Compte de destination',account||'bank','text',true,false,S.accounts.filter(a=>a.active))}${field('category_id','Catégorie par défaut','','text',false,false,[['','À choisir ligne par ligne'],...S.categories.filter(c=>c.active).map(c=>[c.id,c.direction+' · '+c.name])])}${field('header_row','Ligne d’en-tête (CSV / XLSX)','1','number')}${field('sheet','Nom de la feuille Excel (vide = première)')}<label class="row full"><input id="auto-tables" type="checkbox">Excel : détecter plusieurs tableaux (en-têtes, formules, contrôles de soldes)</label></div><div id="import-mapping"></div><div id="import-preview"></div>`,analyzeImport,true,'Analyser le fichier')}
async function analyzeImport(p){let f=$('#import-file').files[0];if(!f)throw Error('Choisissez un fichier.');if(f.size>30*1024*1024)throw Error('Maximum 30 Mo.');let mapping={};$$('[data-map]').forEach(el=>mapping[el.dataset.map]=el.value);let r=await api('import-preview',{...p,blob:await fileBase64(f),filename:f.name,auto_tables:$('#auto-tables').checked,mapping});importRows=r.rows;previewWarnings=r.warnings;
 if(r.headers.length){$('#import-mapping').innerHTML=`<h3 style="margin:20px 0 10px">Correspondance des colonnes</h3><div class="form-grid">${[['date','Date'],['label','Libellé'],['amount','Montant signé'],['direction','Sens'],['debit','Débit'],['credit','Crédit'],['category','Catégorie'],['reference','Référence']].map(([key,label])=>`<div class="field"><label for="map-${key}">${label}</label><select id="map-${key}" data-map="${key}">${options([['','Détection automatique'],...r.headers.map((h,i)=>[String(i),h||'Colonne '+(i+1)])],mapping[key]||'')}</select></div>`).join('')}</div><button type="button" id="reanalyze" style="margin:15px 0">Ré-analyser avec cette correspondance</button>`;$('#reanalyze').onclick=()=>analyzeImport(Object.fromEntries(new FormData($('#modal-form')))).catch(e=>$('#modal-error').textContent=e.message)}
 renderImport();$('#modal-submit').textContent='Confirmer les lignes sélectionnées';modalSave=async()=>{let chosen=importRows.filter(r=>r.selected);if(!chosen.length)throw Error('Sélectionnez au moins une ligne.');if(!confirm('Importer '+chosen.length+' opérations après vérification ?'))return;let result=await api('import',{rows:chosen,confirmation:'IMPORTER'});closeModal(true);await load();notify(result.added+' opérations ajoutées ; '+result.skipped+' doublons ignorés.')};dirty=true;
}
function renderImport(){let display=importRows.map((r,i)=>`<tr class="${r.errors?.length?'import-error':''}"><td><input type="checkbox" data-import-i="${i}" data-import-key="selected" ${r.selected?'checked':''} aria-label="Importer la ligne ${i+1}"></td><td><input type="date" data-import-i="${i}" data-import-key="date" value="${esc(r.date)}" aria-label="Date ligne ${i+1}"></td><td><input data-import-i="${i}" data-import-key="label" value="${esc(r.label)}" aria-label="Libellé ligne ${i+1}"><small class="cell-sub">${esc(r.source||'')}</small></td><td><input data-import-i="${i}" data-import-key="amount" value="${esc(r.amount)}" aria-label="Montant ligne ${i+1}"></td><td><select data-import-i="${i}" data-import-key="direction" aria-label="Sens ligne ${i+1}">${options([['','Choisir'],['Recette','Recette'],['Dépense','Dépense'],['Virement','Virement']],r.direction)}</select></td><td><select data-import-i="${i}" data-import-key="category_id" aria-label="Catégorie ligne ${i+1}">${options([['','Choisir'],...S.categories.filter(c=>c.active).map(c=>[c.id,c.direction+' · '+c.name])],r.category_id)}</select></td><td><select data-import-i="${i}" data-import-key="target_id" aria-label="Destination ligne ${i+1}">${options([['','Sans destination'],...S.accounts.filter(a=>a.active).map(a=>[a.id,a.name])],r.target_id)}</select></td><td class="cell-label">${esc([...(r.errors||[]),...(r.warnings||[]),r.duplicate?'Doublon possible : exclu par défaut':''].filter(Boolean).join(' · '))}</td></tr>`).join('');$('#import-preview').innerHTML=`${previewWarnings.length?`<div class="notice">${previewWarnings.map(esc).join('\n')}</div>`:''}<div class="selected-total">${importRows.length} lignes proposées. Corrigez les cellules, puis cochez les lignes à conserver. Une erreur sur une ligne sélectionnée bloque tout l’import.</div><div class="row"><button type="button" data-action="select-valid-import">Cocher les lignes valides</button><button type="button" data-action="select-none-import">Tout décocher</button></div><div class="table-wrap"><table data-no-sort="1"><thead><tr><th>Inclure</th><th>Date</th><th>Libellé / source</th><th>Euros</th><th>Sens</th><th>Catégorie</th><th>Destination virement</th><th>Contrôles initiaux</th></tr></thead><tbody>${display}</tbody></table></div>`}
function recurrence(e){let prepared=null;const prepare=async p=>{let r=await api('recurrence-preview',{id:e.id,start:p.start,count:Number(p.count),interval:Number(p.interval),unit:p.unit});prepared=r.rows;$('#recurrence-preview').innerHTML='<div class="notice">'+prepared.map(r=>date(r.date)+' · '+esc(r.label)+' · '+money(e.amount)+(r.error?' · '+esc(r.error):'')).join('<br>')+'</div>';if(prepared.some(r=>r.error)){prepared=null;throw Error('Corrigez les dates ou ouvrez les exercices manquants avant de confirmer.')}$('#modal-submit').textContent='Confirmer la série';modalSave=async()=>{if(!prepared)throw Error('Prévisualisez la série.');let r=await api('import',{confirmation:'IMPORTER',rows:prepared});closeModal(true);await load();notify(r.added+' opérations ajoutées.')}};openModal('Répéter une opération',`<div class="notice">Préparez des cotisations, loyers de salle ou charges régulières. Les écritures futures entrent dans la trésorerie projetée. Les fins de mois sont ajustées au dernier jour disponible.</div><div class="form-grid">${field('start','Première date',today(),'date',true)}${field('count','Occurrences (1 à 120)','12','number',true)}${field('unit','Fréquence','month','text',true,false,[['week','Semaines'],['month','Mois'],['year','Années']])}${field('interval','Tous les… (1 à 24)','1','number',true)}</div><div id="recurrence-preview"></div>`,prepare,false,'Prévisualiser');$('#modal-form').addEventListener('input',()=>{prepared=null;modalSave=prepare;$('#modal-submit').textContent='Prévisualiser';$('#recurrence-preview').innerHTML=''})}

function reconcile(id){let a=S.accounts.find(a=>a.id===id);openModal('Comparer au relevé — '+esc(a.name),`<div class="notice">Pointez d’abord les opérations retrouvées sur le relevé. La comparaison ne crée aucune écriture d’ajustement.</div>${field('date','Date du relevé',today(),'date',true)}${field('balance','Solde du relevé en euros','','text',true)}<div id="reconcile-result"></div>`,async p=>{let value=parseCents(p.balance);let computed=balance(a,p.date,true);$('#reconcile-result').innerHTML=`<div class="notice">Solde pointé : ${money(computed)}<br>Solde du relevé : ${money(value)}<br><strong class="${value===computed?'green':'red'}">Écart : ${money(value-computed)}</strong></div>`},false,'Comparer')}
function parseCents(v){let s=String(v).replace(/[\s€]/g,'').replace(',','.');if(!/^[+-]?\d+(\.\d{1,2})?$/.test(s))throw Error('Montant invalide.');let sign=s.startsWith('-')?-1:1;let [a,b='']=s.replace(/^[+-]/,'').split('.');let n=sign*(Number(a)*100+Number(b.padEnd(2,'0')));if(!Number.isSafeInteger(n))throw Error('Montant hors limites.');return n}
async function action(a,id){let e=S.entries.find(e=>e.id===id);switch(a){
 case'new-entry':entryForm();break;case'edit-entry':entryForm(e);break;case'duplicate':entryForm(e,true);break;
 case'delete-entry':confirmAction('Supprimer cette opération',esc(e.label)+' · '+money(e.amount)+'. Une sauvegarde de précaution sera créée. Les justificatifs sont conservés sans lien.','delete-entry',{id,revision:e.revision});break;
 case'new-account':accountForm();break;case'edit-account':accountForm(S.accounts.find(a=>a.id===id));break;case'transfer':entryForm({direction:'Virement',account_id:id,payment:'Virement'});break;
 case'account-journal':account=id;page='journal';render();break;case'reconcile':reconcile(id);break;
 case'new-category':categoryForm();break;case'edit-category':categoryForm(S.categories.find(c=>c.id===id));break;
 case'new-budget':budgetForm();break;case'edit-budget':budgetForm(S.budgets.find(b=>b.id===id));break;
 case'new-period':{let year=Number(S.periods.map(p=>p.end.slice(0,4)).sort().at(-1)||new Date().getFullYear())+1;openModal('Nouvel exercice',`<div class="form-grid">${field('name','Nom',String(year),'text',true,true)}${field('start','Début',year+'-01-01','date',true)}${field('end','Fin',year+'-12-31','date',true)}</div>`,p=>saved('period',p));break}
 case'close-period':confirmAction('Clôturer l’exercice','Les écritures de cet exercice seront verrouillées. Vérifiez les relevés, le pointage et les justificatifs. Une sauvegarde est créée.','close-period',{id});break;
 case'reopen-period':confirmAction('Réouvrir l’exercice','Cette action est enregistrée dans l’historique. Une sauvegarde est créée.','reopen-period',{id},'CONFIRMER',field('reason','Motif de réouverture','','text',true,true));break;
 case'new-document':documentForm();break;case'attach-entry':if(dirty&&!confirm('Abandonner les modifications de cette opération avant de joindre un document ?'))break;closeModal(true);documentForm(id);break;case'preview-document':await previewDocument(id);break;case'document-export':await download('document-export',{id});break;
 case'import':importModal();break;case'export':exportModal();break;case'pdf':await download('export',{format:'pdf',period:period==='all'?'':period,account});break;case'audit-export':await download('export',{format:'audit'});break;
 case'select-valid-import':importRows.forEach(r=>r.selected=!r.errors?.length&&!r.duplicate);renderImport();break;case'select-none-import':importRows.forEach(r=>r.selected=false);renderImport();break;
 case'backup':await api('backup',{});await load();notify('Sauvegarde complète créée et vérifiée.');break;case'backup-export':await download('backup',{export:true});await load();break;
 case'restore-file':restoreModal();break;case'restore-backup':restoreModal(id);break;case'integrity':await api('integrity',{});notify('Intégrité SQLite, relations, exercices et empreintes des justificatifs vérifiés.');break;
 case'theme':await api('settings',{theme:S.settings.theme==='dark'?'light':'dark'});await load();break;case'density':await api('settings',{density:S.settings.density==='compact'?'normal':'compact'});await load();break;
 case'motion':await api('settings',{motion:S.settings.motion==='off'?'auto':'off'});cancelMotion();await load();break;
 case'owner':openModal('Nom du club',field('owner','Nom affiché',S.settings.owner,'text',true),p=>saved('settings',p));break;
 case'prev':pageNumber=Math.max(0,pageNumber-1);render();break;case'next':pageNumber++;render();break;
 case'close-modal':closeModal();break;case'check-update':await api('check-update',{});notify('Vérification lancée.');setTimeout(pollUpdates,1500);break;
 case'recurrence':if(dirty&&!confirm('Abandonner les modifications et préparer une série depuis la dernière version enregistrée ?'))break;closeModal(true);recurrence(e);break;
}}
document.addEventListener('click',e=>{let nav=e.target.closest('[data-page]');if(nav){page=nav.dataset.page;query='';direction='';pageNumber=0;render();return}let th=e.target.closest('th.sortable');if(th){tableSortCycle(th);return}let b=e.target.closest('[data-action]');if(b){e.preventDefault();Promise.resolve(action(b.dataset.action,b.dataset.id)).catch(e=>notify(e.message,true))}});
document.addEventListener('input',e=>{if(e.target.closest('#modal'))dirty=true;if(e.target.dataset.importKey){let r=importRows[Number(e.target.dataset.importI)];r[e.target.dataset.importKey]=e.target.type==='checkbox'?e.target.checked:e.target.value}if(e.target.id==='search'){let focus=e.target.selectionStart;query=e.target.value;pageNumber=0;render();$('#search').focus();$('#search').setSelectionRange(focus,focus)}if(e.target.id==='doc-search'){$$('[data-doc-search]').forEach(el=>el.hidden=!el.dataset.docSearch.includes(e.target.value.toLowerCase()))}});
document.addEventListener('change',e=>{if(e.target.id==='period-filter'){period=e.target.value;pageNumber=0;render()}if(e.target.id==='account-filter'){account=e.target.value;pageNumber=0;render()}if(e.target.id==='direction-filter'){direction=e.target.value;pageNumber=0;render()}});
document.addEventListener('keydown',e=>{if(e.key==='Escape')closeModal();if((e.key==='Enter'||e.key===' ')&&e.target.matches('th.sortable')){e.preventDefault();tableSortCycle(e.target)}if(e.key==='Tab'&&$('#modal').innerHTML){let f=$$('button,input,select,textarea,a[href]',$('#modal')).filter(x=>!x.disabled&&x.offsetParent!==null);if(!f.length)return;if(e.shiftKey&&document.activeElement===f[0]){e.preventDefault();f.at(-1).focus()}else if(!e.shiftKey&&document.activeElement===f.at(-1)){e.preventDefault();f[0].focus()}}});
window.mmaCanClose=()=>!dirty||confirm('Des modifications ne sont pas enregistrées. Les abandonner et quitter ?');
async function pollUpdates(){try{let u=await api('update');if($('#update-status'))$('#update-status').textContent=u.message;if(u.status==='available'&&updateDismissed!==u.latest&&!$('#modal').innerHTML){updateDismissed=u.latest;openModal('Mise à jour '+esc(u.latest),'<p>Une nouvelle version stable est disponible sur GitHub. Les données et les sauvegardes restent à leur emplacement. Le programme redémarrera après installation.</p>',async()=>{await api('install-update',{confirmation:'INSTALLER'});closeModal(true);notify('Téléchargement en cours ; gardez l’application ouverte.')},false,'Installer et redémarrer')}if(u.status==='error'&&updateDismissed!==u.message){updateDismissed=u.message;notify(u.message,true)}}catch(e){/* la fermeture du serveur termine le polling */}}
__SORT_JS__
load().catch(e=>{$('#main').innerHTML='<div class="app-error">Impossible d’ouvrir la comptabilité : '+esc(e.message)+'</div>'});setInterval(pollUpdates,4000);
</script></body></html>'''

CLOSE_LOCK=threading.Lock()


def recover_database(folder, raw, confirmation):
    """Récupération d'une base illisible : conserver l'original, reconstruire le schéma."""
    if confirmation!='RESTAURER': raise ValueError('Saisissez RESTAURER.')
    folder=Path(folder).resolve()
    if not raw.startswith(b'SQLite format 3\0') or len(raw)>500*1024*1024: raise ValueError('Sauvegarde SQLite invalide.')
    staging=folder/('.recuperation-'+uid()); staging.mkdir()
    rebuilt=Store(staging)
    # La restauration valide les données et les insère dans notre propre schéma.
    rebuilt.restore(raw,'RESTAURER')
    quarantine=folder/'recuperation'; quarantine.mkdir(exist_ok=True)
    original=folder/'Data.db'; saved=quarantine/(dt.datetime.now().strftime('%Y%m%d-%H%M%S-%f')+'-original.db')
    moved=False
    try:
        if original.exists(): os.replace(original,saved); moved=True
        os.replace(rebuilt.path,original)
    except Exception:
        if moved: os.replace(saved,original)
        raise
    return str(saved) if moved else ''


def recovery_window(folder,error):
    import webview
    class RecoveryAPI:
        def restore(self,confirmation):
            try:
                if confirmation!='RESTAURER': raise ValueError('Saisissez RESTAURER.')
                chosen=window.create_file_dialog(webview.FileDialog.OPEN,file_types=('Sauvegarde SQLite (*.db)',))
                if not chosen: return {'cancelled':True}
                path=Path(chosen[0])
                if path.stat().st_size>500*1024*1024: raise ValueError('Sauvegarde limitée à 500 Mo.')
                saved=recover_database(folder,path.read_bytes(),confirmation)
                return {'ok':True,'message':'Sauvegarde restaurée. Fermez cette fenêtre puis relancez MMA Comptabilité. Original conservé : '+saved}
            except Exception as exc: return {'error':str(exc)}
    content='''<!doctype html><html lang="fr"><meta charset="utf-8"><title>Récupération MMA Comptabilité</title>
    <style>body{font:15px Arial;background:#151517;color:#f4f3f4;padding:40px;line-height:1.6}h1{font:30px Georgia}p{overflow-wrap:anywhere}input,button{padding:12px;border:1px solid #555;border-radius:6px;background:#242428;color:white}button{background:#bd233b;cursor:pointer}#result{white-space:pre-wrap}</style>
    <h1>Protéger et récupérer vos données</h1><p>La base n’a pas pu être ouverte. Elle n’a pas été réinitialisée.</p><p>__ERROR__</p>
    <p>Sauvegardes : __PATH__</p><p>Une restauration remplace les données actives par la copie choisie. Le fichier original est conservé dans le dossier recuperation.</p>
    <label>Saisissez RESTAURER <input id="confirm" autocomplete="off"></label><button id="restore">Choisir une sauvegarde</button><p id="result" role="status"></p>
    <script>document.querySelector('#restore').onclick=async()=>{let b=document.querySelector('#restore');b.disabled=true;try{let r=await window.pywebview.api.restore(document.querySelector('#confirm').value);document.querySelector('#result').textContent=r.error||r.message||'Sélection annulée.'}catch(e){document.querySelector('#result').textContent=e.message}finally{b.disabled=false}};</script></html>'''
    content=content.replace('__ERROR__',html.escape(str(error))).replace('__PATH__',html.escape(str(folder/'sauvegardes')))
    window=webview.create_window(APP_NAME+' — Récupération',html=content,js_api=RecoveryAPI(),width=850,height=600)
    webview.start(gui='edgechromium' if os.name=='nt' else None)


def main():
    global STORE,SERVER,WINDOW
    parser=argparse.ArgumentParser(description=APP_NAME)
    parser.add_argument('--data-dir',default=str(data_directory()))
    parser.add_argument('--no-update',action='store_true')
    parser.add_argument('--test-server',action='store_true',help='Serveur de test explicite, sans ouverture de navigateur')
    parser.add_argument('--port',type=int,default=0)
    parser.add_argument('--smoke-seconds',type=int,default=0,help='Fermer automatiquement après contrôle de la fenêtre native')
    parser.add_argument('--update-ready'); parser.add_argument('--update-nonce')
    parser.add_argument('--apply-update')
    args=parser.parse_args()
    if args.apply_update: return apply_update(args.apply_update)
    folder=Path(args.data_dir).resolve(); folder.mkdir(parents=True,exist_ok=True)
    logging.basicConfig(filename=folder/'application.log',level=logging.INFO,format='%(asctime)s %(levelname)s %(message)s')
    guard=InstanceGuard(folder)
    try:
        try: STORE=Store(folder)
        except (ValueError,sqlite3.DatabaseError) as exc:
            if args.test_server: raise
            recovery_window(folder,exc)
            return 1
        try: STORE.backup('auto')
        except Exception as e: STORE.backup_error=str(e)
        SERVER=ThreadingHTTPServer(('127.0.0.1',args.port),Handler); SERVER.daemon_threads=True
        threading.Thread(target=SERVER.serve_forever,daemon=True).start()
        threading.Thread(target=backup_loop,daemon=True).start()
        if not args.no_update and not args.test_server: threading.Thread(target=check_updates,daemon=True).start()
        url=f'http://127.0.0.1:{SERVER.server_port}/?token={TOKEN}'
        if args.test_server:
            print(url,flush=True)
            while not STOP.wait(.5): pass
            return 0
        import webview
        WINDOW=webview.create_window(APP_NAME+' — MMA Fight Club Calais',url,width=1440,height=940,min_size=(900,650),background_color='#111113')
        WINDOW.events.closing+=on_closing
        def loaded():
            if args.update_ready and args.update_nonce:
                # Confirmer aussi le chargement fonctionnel de l'interface, pas
                # seulement la création de la fenêtre ou la réponse HTTP.
                deadline=time.monotonic()+25
                while time.monotonic()<deadline:
                    if WINDOW.evaluate_js('Boolean(window.S && document.querySelector(".page-head"))'): break
                    time.sleep(.1)
                else: return
                receipt=Path(args.update_ready); temp=receipt.with_suffix('.tmp')
                temp.write_text(json.dumps({'version':APP_VERSION,'nonce':args.update_nonce}),encoding='utf-8'); os.replace(temp,receipt)
            if args.smoke_seconds:
                def smoke():
                    try:
                        result=WINDOW.evaluate_js('({title:document.title,ready:!!window.S,body:document.body.innerText.slice(0,300)})')
                        (folder/'native-smoke.json').write_text(json.dumps(result,ensure_ascii=False),encoding='utf-8')
                    finally: WINDOW.destroy()
                threading.Timer(args.smoke_seconds,smoke).start()
        WINDOW.events.loaded+=loaded
        if sys.platform=='darwin':
            from AppKit import NSApplication,NSImage
            from Foundation import NSData
            icon=NSImage.alloc().initWithData_(NSData.dataWithBytes_length_(LOGO_PNG,len(LOGO_PNG)))
            NSApplication.sharedApplication().setApplicationIconImage_(icon)
        webview.start(gui='edgechromium' if os.name=='nt' else None,debug=False)
        return 0
    finally:
        STOP.set()
        if SERVER: SERVER.shutdown(); SERVER.server_close()
        guard.close()


# === Lecteurs et composants conservés de Dominis (voir docs/ANALYSE.md) ===
class InstanceGuard:
    """Une seule instance locale par dossier du programme, même sur un autre port."""
    def __init__(self, folder):
        self.file = open(Path(folder) / '.mma-instance.lock', 'a+b')
        try:
            self.file.seek(0, 2)
            if self.file.tell() == 0:
                self.file.write(b'0'); self.file.flush()
            self.file.seek(0)
            if os.name == 'nt':
                import msvcrt
                msvcrt.locking(self.file.fileno(), msvcrt.LK_NBLCK, 1)
            else:
                import fcntl
                fcntl.flock(self.file.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
        except Exception:
            self.file.close()
            raise

    def close(self):
        self.file.close()  # La fermeture libère le verrou sur les deux plateformes.


XLSX_MAX_RECORDS = 10000
# Nombre maximum de rappels datés réglable depuis une échéance (l'interface en propose 30 par défaut).
MAX_TASK_REMINDERS = 365
_XL_DATE_NUMFMT = {14,15,16,17,18,19,20,21,22,27,28,29,30,31,32,33,34,35,36,45,46,47,50,51,52,53,54,55,56,57,58}
_XL_ACCENTS = str.maketrans({'à':'a','â':'a','ä':'a','ç':'c','é':'e','è':'e','ê':'e','ë':'e','î':'i','ï':'i','ô':'o','ö':'o','ù':'u','û':'u','ü':'u','œ':'oe','ÿ':'y'})
_XL_SPACES = '\u00a0\u202f\u2009\u200b\u3000 \t\r\n\'’'
_XL_GENERIC_SHEET = re.compile(r'^(?:feuilles?|feuils?|sheets?|classeurs?|csv)\s*\d*$', re.I)
_XL_YEAR_ONLY = re.compile(r'^(?:ann[eé]es?\s+|exercices?\s+|comptes?\s+| relev[eé]s?\s+)?(19\d\d|20\d\d)$', re.I)
_XL_MONTHS = {
    'janvier': 1, 'janv': 1, 'jan': 1,
    'fevrier': 2, 'fevr': 2, 'fev': 2,
    'mars': 3, 'mar': 3,
    'avril': 4, 'avr': 4,
    'mai': 5,
    'juin': 6, 'jun': 6,
    'juillet': 7, 'juil': 7, 'jul': 7,
    'aout': 8, 'aou': 8,
    'septembre': 9, 'sept': 9, 'sep': 9,
    'octobre': 10, 'oct': 10,
    'novembre': 11, 'nov': 11,
    'decembre': 12, 'dec': 12,
}
_XL_BALANCE_RE = re.compile(
    r'^(?:solde\b|ancien\s+solde\b|nouveau\s+solde\b|report\s+(?:a\s+)?nouveau\b|report\b|'
    r'totaux\b|total\b|sous[\s\-]*total\b|cumul\b|bilan\b|fin\s+de\s+mois\b|debut\s+de\s+mois\b)',
    re.I,
)
_XL_PERIOD_SUBTITLE_RE = re.compile(
    r'^(?:(?:mois\s+(?:de\s+|d\s*))?(?:janvier|fevrier|mars|avril|mai|juin|juillet|aout|septembre|octobre|novembre|decembre)'
    r'(?:\s+(?:19\d\d|20\d\d))?|(?:ann[eé]e\s+|exercice\s+|trimestre\s+|semestre\s+)?(?:19\d\d|20\d\d))$',
    re.I,
)


def _x_local(el):
    return el.tag.split('}', 1)[-1]


def _x_present(value):
    return value is not None and (not isinstance(value, str) or value.strip() != '')


def _x_norm(value):
    if value is None: return ''
    return ' '.join(str(value).lower().translate(_XL_ACCENTS).replace('’', ' ').replace("'", ' ').split())


def _x_is_balance_label(value):
    if not isinstance(value, str): return False
    s = _x_norm(value)
    return bool(_XL_BALANCE_RE.match(s))


def _x_is_debit_balance_label(value):
    if not _x_is_balance_label(value): return False
    s = _x_norm(value)
    return 'debiteur' in s or 'negatif' in s

# Mots qui n'apportent pas d'information métier dans un intitulé de contrôle :
# « Solde créditeur au 30/06/2026 » ne contient que des mots de contrôle, alors
# que « Total travaux salle de bain » est une véritable opération.
_XL_BALANCE_QUALIFIERS = re.compile(
    r'\b(?:crediteur|cred|crediteurs|debiteur|deb|debiteurs|negatif|negative|general|generale|'
    r'cumule|cumulee|cumules|report|nouveau|ancien|ancienne|solde|soldes|totaux|total|'
    r'sous|bilan|cumul|au|a|du|de|des|le|la|les|en|et|fin|debut|mois|jour|operation|operations|'
    r'mouvement|mouvements|compte|banque|annee|exercice|aujourd|hui|arret|arrete|arretes|'
    r'present|precedent|reporte|a\s+nouveau)\b'
)
_XL_MONTH_WORDS = re.compile(
    r'\b(?:janvier|fevrier|mars|avril|mai|juin|juillet|aout|septembre|octobre|novembre|decembre)\b'
)
_XL_DATE_FRAGMENT = re.compile(r'\d{1,4}\s*[/.\-]\s*\d{1,2}(?:\s*[/.\-]\s*\d{1,4})?')


def _x_balance_label_kind(value):
    """Classe un intitulé de contrôle : None (pas un contrôle) ou 'solde'.

    Un intitulé n'est un contrôle que s'il ne reste, une fois retirés les mots
    de contrôle et les dates, aucun mot métier. « Solde créditeur au 31/01 »
    est un contrôle ; « Total travaux » ou « Report charges » sont des
    opérations et ne doivent jamais être supprimées à l'import.
    """
    if not isinstance(value, str): return None
    text = _x_norm(value)
    if not text or not _XL_BALANCE_RE.match(text): return None
    rest = _XL_DATE_FRAGMENT.sub(' ', text)
    rest = _XL_MONTH_WORDS.sub(' ', rest)
    rest = re.sub(r'\b\d+\b', ' ', rest)
    rest = _XL_BALANCE_QUALIFIERS.sub(' ', rest)
    rest = re.sub(r'[^a-z]+', ' ', rest).strip()
    return None if rest else 'solde'


# Proposition de catégorie à partir du libellé d'une opération. Le classeur
# importé ne contient presque jamais de colonne « Catégorie » : sans cette
# étape, ni l'analyse ni les graphiques par catégorie ne peuvent fonctionner.
_XL_CATEGORY_RULES = [
    (re.compile(r'\b(?:depot\s+de\s+garantie|caution|garantie\s+locative)\b'), 'Dépôt de garantie'),
    (re.compile(r'\b(?:remboursement\s+(?:associe|associes|compte\s+courant))\b'), 'Remboursement associé'),
    (re.compile(r'\b(?:apport|associe|associes|capital\s+social)\b'), 'Apport associé'),
    (re.compile(r'\b(?:taxe\s+fonciere|impot|impots|fiscal|tva|cfp|taxe)\b'), 'Taxe foncière'),
    (re.compile(r'\b(?:assurance|pno|axa|maif|mma|generali|aviva|allianz|swisslife)\b'), 'Assurance'),
    (re.compile(r'\b(?:honoraire|honoraires|frais\s+de\s+gestion|agence|syndic\s+honoraires)\b'), 'Frais de gestion'),
    (re.compile(r'\b(?:echeance|emprunt|pret|credit|interet|interets|banque|frais\s+bancaire)\b'), 'Emprunt (capital + intérêts)'),
    (re.compile(r'\b(?:travaux|renovation|reparation|plombier|electricien|peinture|toiture|chaufferie|ravalement|menuiserie)\b'), 'Travaux'),
    (re.compile(r'\b(?:entretien|jardin|nettoyage|menage|ascenseur|chauffage)\b'), 'Entretien'),
    (re.compile(r'\b(?:charges?\s+(?:de\s+)?copro|charges|copropriete|copro|provision)\b'), 'Provisions de charges'),
    (re.compile(r'\b(?:loyer|loyers|location|locatif|bail|quittance|virement\s+(?:mle|mlle|mr|mme|sci|sarl))\b'), 'Loyers'),
]


def _x_guess_category(label):
    """Catégorie probable d'une opération, ou None si le libellé ne dit rien."""
    text = _x_norm(label)
    if not text: return None
    for pattern, category in _XL_CATEGORY_RULES:
        if pattern.search(text): return category
    return None


def _x_find_year(value):
    if not value: return None
    m = re.search(r'(?<!\d)(19\d\d|20\d\d)(?!\d)', str(value))
    return int(m.group(1)) if m else None


def _x_col_letter(col_idx):
    if col_idx is None or col_idx < 0: return '?'
    n, out = int(col_idx) + 1, ''
    while n > 0:
        n, rem = divmod(n - 1, 26)
        out = chr(65 + rem) + out
    return out


def _x_eur(value):
    intp, dec = f'{abs(value):.2f}'.split('.')
    intp = re.sub(r'(\d)(?=(\d{3})+(?!\d))', r'\1 ', intp)
    return ('-' if value < 0 else '') + intp + ',' + dec + ' €'


def _x_header_kinds(cells):
    """Reconnaît l'en-tête d'un tableau (toutes colonnes identifiées par leur nom).

    Deux organisations sont acceptées : Débit + Crédit, ou une seule colonne
    « Montant » accompagnée d'une colonne « Sens ».
    """
    kinds = {}
    for col in sorted(cells):
        value = cells[col]
        if not isinstance(value, str): continue
        s = ' '.join(value.lower().translate(_XL_ACCENTS).split())
        if not s: continue
        kind = None
        if 'date' in s: kind = 'date'
        elif any(t in s for t in ('libell', 'label', 'description', 'operation', 'intitul', 'nature', 'objet')): kind = 'label'
        elif 'debit' in s or re.search(r'\bd.?bit\b', s): kind = 'debit'
        elif 'credit' in s or re.search(r'\bcr.?dit\b', s): kind = 'credit'
        elif 'solde' in s or 'balance' in s: kind = 'solde'
        elif 'categorie' in s or 'category' in s or re.search(r'\bcat.?gorie\b', s): kind = 'category'
        elif re.search(r'\bmontants?\b', s) or re.search(r'\bamount\b', s) or re.search(r'\bvaleurs?\b', s): kind = 'amount'
        elif re.search(r'\bsens\b', s) or re.search(r'\bdirections?\b', s): kind = 'sens'
        if kind and kind not in kinds: kinds[kind] = col
    if not all(k in kinds for k in ('date', 'label')): return None
    if all(k in kinds for k in ('debit', 'credit')) or 'amount' in kinds: return kinds
    return None


def _x_header_merge(previous, current):
    """En-tête écrit sur deux lignes (cellules fusionnées) : « Date · Libellé » puis « Débit · Crédit ».

    Renvoie les cellules fusionnées quand elles forment un en-tête complet, sinon None.
    """
    if not previous or not current: return None
    if any(isinstance(v, (int, float, dt.date, dt.datetime)) and not isinstance(v, bool)
           for v in list(previous.values()) + list(current.values())):
        return None
    if _x_header_kinds(current): return None      # en-tête complet : rien à fusionner
    merged = dict(previous)
    merged.update(current)
    return merged if _x_header_kinds(merged) else None


_XL_SUMMARY_RE = re.compile(
    r'^(?:totaux|total|sous[\s\-]*total|cumul|recapitulatif|recap|bilan|synthese|montant\s+total)\b')
_XL_SUMMARY_GENERIC = re.compile(
    r'\b(?:depenses|depense|recettes|recette|debits|debit|credits|credit|mouvements|mouvement|'
    r'operations|operation|charges|charge|produits|produit|entrees|entree|sorties|sortie|'
    r'general|generale|generaux|annuel|annuelle|annuels|annuelles|mensuel|mensuelle|mensuels|mensuelles|'
    r'annee|annees|exercice|exercices|mois|periode|banque|compte|comptes|releve|releves|'
    r'du|de|des|le|la|les|en|et|au|aux|a|sur|pour|par|d|du|cumul|totaux|total|sous|'
    r'janvier|fevrier|mars|avril|mai|juin|juillet|aout|septembre|octobre|novembre|decembre)\b'
)


def _x_summary_label(value):
    """Ligne de synthèse (« Total des dépenses », « Cumul annuel ») : jamais une opération.

    Comme pour les libellés de contrôle, un libellé qui conserve un mot métier
    (« Total travaux salle de bain ») reste une véritable opération.
    """
    if not isinstance(value, str): return False
    text = _x_norm(value)
    if not text or not _XL_SUMMARY_RE.match(text): return False
    text = _XL_DATE_FRAGMENT.sub(' ', text)
    text = re.sub(r'\b\d+(?:[.,]\d+)?\b', ' ', text)
    text = _XL_SUMMARY_GENERIC.sub(' ', text)
    return not re.sub(r'[^a-z]+', ' ', text).strip()


_XL_SENS_DEBIT = {'debit', 'debits', 'depense', 'depenses', 'sortie', 'sorties', 'retrait', 'retraits',
                  'prelevement', 'prelevements', 'emission', 'emissions', 'd', 'db', 'dr', '-', '−', 'achat'}
_XL_SENS_CREDIT = {'credit', 'credits', 'recette', 'recettes', 'entree', 'entrees', 'versement',
                   'versements', 'depot', 'depots', 'encaissement', 'encaissements', 'c', 'cr', '+',
                   'produit', 'vente'}


_XL_FOOTER_STRONG = re.compile(r'^(?:recapitulatif|recap|synthese|bilan\b|total\s+general|totaux\s+generaux)')

# Onglets qui récapitulent l'ensemble sans contenir un relevé bancaire : leurs
# montants sont des agrégats déjà présents dans les feuilles de détail. Les lire
# comme des opérations créait une SCI fantôme et doublait les montants.
# Noms d'onglets écartés d'office : assez explicites pour ne jamais désigner un
# relevé bancaire. « Recap », « Bilan » ou « Analyse » restent acceptés comme
# feuilles de données (trop ambigus) ; c'est le titre du tableau qui tranche.
_XL_SUMMARY_SHEET = re.compile(
    r'^(?:syntheses?|recapitulatifs?|resumes?|tableau\s+de\s+bord|dashboards?|'
    r'statistiques?|vue\s+d\s*ensemble|bilan\s+general|totaux?\s+genera(?:l|ux))\b'
)
# Titres de tableau qui annoncent un récapitulatif : plus larges que les noms
# d'onglets, car un titre n'est jamais un nom de société.
_XL_SUMMARY_TITLE = re.compile(
    r'^(?:syntheses?|recapitulatifs?|recap|resumes?|tableau\s+de\s+bord|dashboards?|'
    r'statistiques?|stats|analyse|bilan\s+general|totaux?\s+genera(?:l|ux)|'
    r'vue\s+d\s*ensemble|ensemble)\b'
)
_XL_ENTITY_RE = re.compile(r'\b(?:sci|societe|sarl|sas|scp|scpi|gfa|indivision)\b')


def _x_is_summary_sheet(name):
    """Feuille de synthèse (« Synthèse », « Récapitulatif », « Tableau de bord »)."""
    text = _x_norm(name or '').strip(' .:-_')
    return bool(text) and bool(_XL_SUMMARY_SHEET.match(text))


def _x_is_summary_title(text):
    """Titre de tableau qui n'annonce aucune SCI (« Récapitulatif général »)."""
    norm = _x_norm(text or '')
    if not norm: return False
    return bool(_XL_SUMMARY_TITLE.match(norm)) and not _XL_ENTITY_RE.search(norm)


def _x_strip_control_prefix(text):
    """« Bilan 2024 · SCI THEMA » → « SCI THEMA » (le nom de la SCI est conservé).

    Un titre qui commence par un mot de contrôle (bilan, total, cumul, solde,
    récapitulatif…) était écarté en entier : le tableau perdait alors le nom de
    sa société et deux feuilles annuelles créaient deux SCI distinctes.
    """
    if not isinstance(text, str): return text
    raw = ' '.join(text.split())
    if not raw or not _XL_BALANCE_RE.match(_x_norm(raw)): return raw
    if not _XL_ENTITY_RE.search(_x_norm(raw)): return raw
    # On coupe au premier séparateur qui précède le nom de la société.
    parts = re.split(r'\s+[·•\-–—:|/]\s+|\s*[·•]\s*', raw)
    for idx, part in enumerate(parts):
        m = re.search(r'\b(?:SCI|SCPI|SARL|SAS|SCP|GFA|Indivision|Soci[eé]t[eé])\b', part, re.I)
        if not m: continue
        head = part[m.start():].strip()
        joined = ' '.join([head] + [q.strip() for q in parts[idx + 1:] if q.strip()])
        return joined or raw
    return raw


def _x_footer_label(value, strong=False):
    """Ligne qui ouvre un bas de tableau : « Récapitulatif », « Total des dépenses », « Synthèse ».

    « Récapitulatif », « Synthèse » ou « Bilan » annoncent un bloc de synthèse
    même si des lignes datées suivent ; « Total janvier » peut n'être qu'un
    intertitre de relevé mensuel, seule la suite permet de trancher.
    """
    if not isinstance(value, str): return False
    text = _x_norm(value)
    if not text: return False
    if strong: return bool(_XL_FOOTER_STRONG.match(text))
    return bool(_XL_SUMMARY_RE.match(text))


def _x_sens_kind(value):
    """Sens d'une opération rangée dans une colonne unique « Montant »."""
    if not isinstance(value, str): return None
    text = _x_norm(value).strip(' .:')
    if not text: return None
    if text in _XL_SENS_DEBIT or text.startswith(('debit', 'depense', 'sortie', 'retrait', 'prelevement')):
        return 'debit'
    if text in _XL_SENS_CREDIT or text.startswith(('credit', 'recette', 'entree', 'versement', 'depot', 'encaissement')):
        return 'credit'
    return None


def _x_amount(value, zero_dash=False, notes=None):
    """Convertit un montant Excel (numérique ou texte français « 32 155,66 € ») en float.

    Un texte comme « 1.234 » (un point suivi de trois chiffres) est lu comme un
    séparateur de milliers, donc 1 234,00 € : un montant bancaire n'a jamais
    trois décimales, alors que le point des milliers est courant. La lecture est
    signalée à l'appelant (`notes`) pour ne rien convertir en silence.
    """
    if value is None or isinstance(value, bool): return None
    if isinstance(value, (dt.datetime, dt.date)): return None
    if isinstance(value, (int, float)):
        v = float(value)
    else:
        raw_str = str(value).strip()
        if not raw_str: return None
        if raw_str.startswith('#') and raw_str.endswith(('!', '?')):
            raise ValueError('montant illisible : erreur de formule Excel « ' + raw_str[:40] + ' »')
        s = raw_str
        paren = s.startswith('(') and s.endswith(')')
        if paren: s = s[1:-1]
        s = s.replace('−', '-').replace('–', '-').replace('—', '-').replace('€', '')
        s = re.sub(r'(?i)\beur\b', '', s)
        for ch in _XL_SPACES: s = s.replace(ch, '')
        if not s: return None
        if re.fullmatch(r'-+', s):
            return 0.0 if zero_dash else None
        sign = -1 if (paren or s.startswith('-')) else 1
        s = s.lstrip('+-')
        if not s:
            return 0.0 if zero_dash else None
        if ',' in s and '.' in s:
            if s.rfind(',') > s.rfind('.'): s = s.replace('.', '').replace(',', '.')
            else: s = s.replace(',', '')
        elif ',' in s:
            s = s.replace(',', '.')
        elif re.fullmatch(r'\d{1,3}\.\d{3}', s):
            if notes is not None: notes.append(raw_str[:40])
            s = s.replace('.', '')
        if not re.fullmatch(r'\d+(?:\.\d+)?', s):
            raise ValueError('montant illisible : « ' + raw_str[:60] + ' »')
        try: v = sign * float(s)
        except ValueError: raise ValueError('montant illisible : « ' + raw_str[:60] + ' »')
    if v != v or not (-1e12 < v < 1e12): raise ValueError('montant hors limites.')
    return v


def _x_date(value, epoch, default_year=None):
    """Date Excel : sérial numérique, cellule date, ISO, ou JJ/MM(/AA[AA]) français."""
    if isinstance(value, dt.datetime): return value.date()
    if isinstance(value, dt.date): return value
    if value is None or isinstance(value, bool): return None
    if isinstance(value, (int, float)):
        v = float(value)
        if v != v or v < 10000 or v > 100000: return None
        try: return epoch + dt.timedelta(days=int(v))
        except (OverflowError, ValueError): return None
    s = str(value).strip()
    if not s: return None
    candidates = [s]
    for sep in ('T', ' '):
        if sep in s: candidates.append(s.split(sep, 1)[0])
    for cand in dict.fromkeys(candidates):
        cand = cand.strip().rstrip('.').strip()
        m = re.fullmatch(r'(\d{4})[/\-.](\d{1,2})[/\-.](\d{1,2})', cand)
        if m:
            try: return dt.date(int(m[1]), int(m[2]), int(m[3]))
            except ValueError: return None
        m = re.fullmatch(r'(\d{1,2})[/\-.](\d{1,2})[/\-.](\d{2,4})', cand)
        if m:
            day, mon, yr = int(m[1]), int(m[2]), int(m[3])
            if yr < 100: yr += 2000 if yr <= 68 else 1900
            try: return dt.date(yr, mon, day)
            except ValueError: return None
        if default_year:
            m = re.fullmatch(r'(\d{1,2})[/\-.](\d{1,2})[/\-.]?', cand)
            if m:
                try: return dt.date(int(default_year), int(m[2]), int(m[1]))
                except ValueError: return None
    norm = _x_norm(s).replace('.', ' ')
    m_txt = re.fullmatch(r'(\d{1,2})(?:er)?\s+([a-z]+)(?:\s+(\d{2,4}))?', norm)
    if m_txt and m_txt.group(2) in _XL_MONTHS:
        day = int(m_txt.group(1))
        mon = _XL_MONTHS[m_txt.group(2)]
        yr = int(m_txt.group(3)) if m_txt.group(3) else default_year
        if yr:
            if yr < 100: yr += 2000 if yr <= 68 else 1900
            try: return dt.date(int(yr), mon, day)
            except ValueError: return None
    if re.fullmatch(r'\d{4,5}(?:\.0+)?', s):
        n = int(float(s))
        if 10000 <= n <= 100000:
            try: return epoch + dt.timedelta(days=n)
            except (OverflowError, ValueError): return None
    return None


def _x_extract_date_from_text(text, epoch, default_year=None):
    """Extrait une date présente dans un libellé de solde (ex. « Solde Créditeur au 01/07/2021 »)."""
    if not text: return None
    direct = _x_date(text, epoch, default_year=default_year)
    if direct is not None: return direct
    s = str(text)
    for m in re.finditer(r'(\d{4}[/\-.]\d{1,2}[/\-.]\d{1,2}|\d{1,2}[/\-.]\d{1,2}[/\-.]\d{2,4})', s):
        d = _x_date(m.group(1), epoch, default_year=default_year)
        if d is not None: return d
    norm = _x_norm(s).replace('.', ' ')
    for m in re.finditer(r'\b(\d{1,2})(?:er)?\s+([a-z]+)(?:\s+(\d{2,4}))?\b', norm):
        if m.group(2) in _XL_MONTHS:
            day = int(m.group(1))
            mon = _XL_MONTHS[m.group(2)]
            yr = int(m.group(3)) if m.group(3) else default_year
            if yr:
                if yr < 100: yr += 2000 if yr <= 68 else 1900
                try: return dt.date(int(yr), mon, day)
                except ValueError: pass
    if default_year:
        for m in re.finditer(r'(?<!\d)(\d{1,2})[/\-.](\d{1,2})(?![/\-.\d])', s):
            try: return dt.date(int(default_year), int(m.group(2)), int(m.group(1)))
            except ValueError: pass
    return None


def _x_col_ref(ref):
    if not ref: return None
    m = re.match(r'([A-Za-z]+)', str(ref))
    if not m: return None
    n = 0
    for ch in m.group(1).upper(): n = n * 26 + (ord(ch) - 64)
    return n - 1


def _x_is_date_numfmt(numfmt_id, custom):
    try: fid = int(numfmt_id)
    except (TypeError, ValueError): return False
    if fid in _XL_DATE_NUMFMT: return True
    code = custom.get(str(fid), '')
    if not code: return False
    code = re.sub(r'"(?:[^"]|"")*"', '', code)
    code = re.sub(r'\\.', '', code)
    code = re.sub(r'\[[^\]]*\]', '', code)
    return bool(re.search(r'[dmyhs]', code, re.I))


def _x_rich_text(el):
    parts = []
    for child in el:
        loc = _x_local(child)
        if loc == 't':
            parts.append(child.text or '')
        elif loc == 'r':
            for sub in child:
                if _x_local(sub) == 't':
                    parts.append(sub.text or '')
    return ''.join(parts)


def _x_shared_strings(zf):
    try: data = zf.read('xl/sharedStrings.xml')
    except KeyError: return []
    out = []
    for event, el in ET.iterparse(io.BytesIO(data), events=('end',)):
        if _x_local(el) == 'si':
            out.append(_x_rich_text(el))
            el.clear()
    return out


def _x_styles(zf):
    """Index de styles dont le format rend une date (conversion des séries Excel)."""
    try: data = zf.read('xl/styles.xml')
    except KeyError: return set()
    try: root = ET.fromstring(data)
    except ET.ParseError: return set()
    custom = {}
    for el in root.iter():
        if _x_local(el) == 'numFmt' and el.get('numFmtId'):
            custom[el.get('numFmtId')] = el.get('formatCode') or ''
    flags = []
    for el in root.iter():
        if _x_local(el) == 'cellXfs':
            for xf in el:
                if _x_local(xf) == 'xf':
                    flags.append(_x_is_date_numfmt(xf.get('numFmtId', '0'), custom))
            break
    return {i for i, flagged in enumerate(flags) if flagged}


def _x_border_styles(zf):
    """Index de styles dont une bordure est tracée (l'étendue d'un tableau).

    Les classeurs bancaires encadrent le tableau des opérations : la dernière
    ligne bordée marque la fin des transactions, tout ce qui suit (synthèse,
    récapitulatif, notes) est hors du tableau et ne doit jamais devenir une
    opération. Si le classeur n'utilise aucune bordure, la détection est neutre.
    """
    empty = {'any': set(), 'bottom': set()}
    try: data = zf.read('xl/styles.xml')
    except KeyError: return empty
    try: root = ET.fromstring(data)
    except ET.ParseError: return empty
    borders, xf_borders = [], []
    for el in root.iter():
        local = _x_local(el)
        if local == 'borders':
            for border in el:
                if _x_local(border) != 'border': continue
                sides = {_x_local(side) for side in border if side.get('style')}
                borders.append(sides)
        elif local == 'cellXfs':
            for xf in el:
                if _x_local(xf) != 'xf': continue
                try: xf_borders.append(int(xf.get('borderId', '0')))
                except (TypeError, ValueError): xf_borders.append(0)
    any_side, bottom = set(), set()
    for index, border_id in enumerate(xf_borders):
        sides = borders[border_id] if 0 <= border_id < len(borders) else set()
        if sides: any_side.add(index)
        if 'bottom' in sides: bottom.add(index)
    return {'any': any_side, 'bottom': bottom}


def _x_sheets(zf):
    """Feuilles dans l'ordre du classeur + époque de sérial Excel."""
    names = set(zf.namelist())
    try: wb = ET.fromstring(zf.read('xl/workbook.xml'))
    except KeyError: raise ValueError('classeur illisible : workbook.xml introuvable.')
    epoch = dt.date(1899, 12, 30)
    for el in wb.iter():
        if _x_local(el) == 'workbookPr' and (el.get('date1904') or '').lower() in ('1', 'true'):
            epoch = dt.date(1904, 1, 1)
    rels = {}
    try:
        rr = ET.fromstring(zf.read('xl/_rels/workbook.xml.rels'))
        for rel in rr.iter():
            if _x_local(rel) == 'Relationship' and rel.get('Id') and rel.get('Target'):
                rels[rel.get('Id')] = rel.get('Target')
    except KeyError:
        rels = {}
    sheets = []
    for el in wb.iter():
        if _x_local(el) != 'sheet' or not el.get('name'): continue
        if (el.get('state') or '').lower() in ('veryhidden',): continue
        rid = None
        for key, val in el.attrib.items():
            if key == 'id' or key.endswith('}id'): rid = val; break
        target = rels.get(rid) or ('worksheets/sheet' + str(len(sheets) + 1) + '.xml')
        target = str(target).replace('\\', '/').lstrip('/')
        path = target if target.startswith('xl/') else 'xl/' + target
        if path not in names:
            raise ValueError('classeur incomplet : feuille « ' + str(el.get('name')) + ' » introuvable.')
        sheets.append((str(el.get('name')), path))
    if not sheets:
        def natkey(p):
            m = re.search(r'(\d+)', p)
            return (int(m.group(1)) if m else 0, p)
        found = sorted((n for n in names if re.fullmatch(r'xl/worksheets/sheet\d+\.xml', n)), key=natkey)
        sheets = [('Feuille ' + str(i + 1), p) for i, p in enumerate(found)]
    if not sheets: raise ValueError('classeur sans feuille de calcul.')
    return sheets, epoch


class _XLFormulaError(Exception):
    """Formule Excel sans valeur en cache et non évaluable simplement."""


_XL_FORMULA_REF = re.compile(r'(\$?)([A-Za-z]{1,3})(\$?)(\d{1,7})')
_XL_FORMULA_NUM = re.compile(r'\d+(?:[.,]\d*)?|[.,]\d+')
_XL_FORMULA_NAME = re.compile(r'[A-Za-z_][A-Za-z0-9_.]*')


def _x_col_letter(index):
    n, out = int(index) + 1, ''
    while n > 0:
        n, rest = divmod(n - 1, 26)
        out = chr(65 + rest) + out
    return out


def _x_formula_tokens(expr):
    """Découpe une formule en jetons (nombres, références, plages, opérateurs, fonctions).

    Toute construction non prise en charge lève _XLFormulaError : une formule
    n'est jamais évaluée « au hasard ».
    """
    text = str(expr or '').strip()
    if text.startswith('='): text = text[1:]
    toks, i, n = [], 0, len(text)
    while i < n:
        ch = text[i]
        if ch in ' \t\r\n': i += 1; continue
        if ch in '+-*/^%&': toks.append(('op', ch)); i += 1; continue
        if ch == '(': toks.append(('lp', '(')); i += 1; continue
        if ch == ')': toks.append(('rp', ')')); i += 1; continue
        if ch in ',;': toks.append(('sep', ch)); i += 1; continue
        if ch == '"':
            j = i + 1
            while j < n:
                if text[j] == '"':
                    if j + 1 < n and text[j + 1] == '"': j += 2; continue
                    break
                j += 1
            if j >= n: raise _XLFormulaError('guillemet non fermé')
            toks.append(('str', text[i + 1:j].replace('""', '"'))); i = j + 1; continue
        if ch.isdigit() or (ch == '.' and i + 1 < n and text[i + 1].isdigit()):
            m = _XL_FORMULA_NUM.match(text, i)
            toks.append(('num', float(m.group(0).replace(',', '.')))); i = m.end(); continue
        ref = _XL_FORMULA_REF.match(text, i)
        if ref is not None and not (ref.end() < n and text[ref.end()] == '('):
            # Lignes numérotées comme dans le fichier (1 = première ligne), colonnes à partir de 0.
            start_row, start_col = int(ref.group(4)), _x_col_ref(ref.group(2))
            i = ref.end()
        else:
            m = _XL_FORMULA_NAME.match(text, i)
            if not m: raise _XLFormulaError('caractère inattendu « ' + ch + ' »')
            name = m.group(0)
            j = m.end()
            while j < n and text[j] in ' \t': j += 1
            if j < n and text[j] == '(':
                toks.append(('func', name.upper())); i = j + 1; continue
            raise _XLFormulaError('référence « ' + name[:20] + ' » non prise en charge')
        if i < n and text[i] == ':':
            second = _XL_FORMULA_REF.match(text, i + 1)
            if not second: raise _XLFormulaError('plage incomplète')
            toks.append(('range', (start_row, start_col, int(second.group(4)), _x_col_ref(second.group(2)))))
            i = second.end()
        else:
            toks.append(('ref', (start_row, start_col)))
        if i < n and text[i] == '!': raise _XLFormulaError('référence vers une autre feuille')
    return toks


def _x_shift_formula(text, drow, dcol):
    """Décale les références relatives d'une formule partagée (« shared »)."""
    def repl(m):
        col_abs, col, row_abs, row = m.group(1), m.group(2), m.group(3), m.group(4)
        new_col = col if col_abs else _x_col_letter(_x_col_ref(col) + dcol)
        new_row = row if row_abs else str(int(row) + drow)
        return col_abs + new_col + row_abs + new_row
    return _XL_FORMULA_REF.sub(repl, text)


def _x_round_half_up(value, digits=0):
    """Arrondi commercial (0,5 s'éloigne de zéro), comme Excel et non comme Python."""
    factor = 10.0 ** int(digits)
    scaled = value * factor
    rounded = math.floor(scaled + 0.5) if scaled >= 0 else math.ceil(scaled - 0.5)
    return rounded / factor


def _x_formula_num(value):
    if isinstance(value, bool): return 1.0 if value else 0.0
    if isinstance(value, (int, float)): return float(value)
    if value is None: return 0.0     # cellule vide : Excel compte zéro
    raise _XLFormulaError('valeur non numérique')


def _x_formula_numbers(args):
    values = []
    for arg in args:
        for value in (arg if isinstance(arg, list) else [arg]):
            if isinstance(value, bool) or value is None or isinstance(value, str): continue
            if isinstance(value, (int, float)): values.append(float(value))
    return values


def _x_formula_func(name, args):
    if name in ('SUM', 'SOMME'): return round(sum(_x_formula_numbers(args)), 10)
    if name == 'ABS':
        if len(args) != 1: raise _XLFormulaError('ABS attend un seul argument')
        return abs(_x_formula_num(args[0]))
    if name == 'MIN':
        values = _x_formula_numbers(args); return min(values) if values else 0.0
    if name == 'MAX':
        values = _x_formula_numbers(args); return max(values) if values else 0.0
    if name in ('AVERAGE', 'MOYENNE'):
        values = _x_formula_numbers(args); return (sum(values) / len(values)) if values else 0.0
    if name in ('ROUND', 'ARRONDI'):
        if not 1 <= len(args) <= 2: raise _XLFormulaError('ROUND attend un ou deux arguments')
        digits = int(_x_formula_num(args[1])) if len(args) > 1 else 0
        return _x_round_half_up(_x_formula_num(args[0]), digits)
    raise _XLFormulaError('fonction ' + name[:20] + ' non prise en charge')


def _x_eval_formula(expr, lookup, lookup_range):
    """Évalue une formule simple : opérations, références, plages et SUM/ABS/ROUND/MIN/MAX.

    Lève _XLFormulaError dès qu'une construction sort de ce périmètre : l'appelant
    signale alors la cellule au lieu d'importer un montant faux.
    """
    toks = _x_formula_tokens(expr)
    if not toks: raise _XLFormulaError('formule vide')
    pos = [0]

    def peek(kind=None):
        if pos[0] >= len(toks): return None
        tok = toks[pos[0]]
        return tok if kind is None else (tok if tok[0] == kind else None)

    def atom():
        tok = peek()
        if tok is None: raise _XLFormulaError('formule incomplète')
        kind, value = tok
        if kind == 'num':
            pos[0] += 1; return value
        if kind == 'str':
            pos[0] += 1; return value
        if kind == 'lp':
            pos[0] += 1
            result = expression()
            if peek('rp') is None: raise _XLFormulaError('parenthèse non fermée')
            pos[0] += 1
            return result
        if kind == 'ref':
            pos[0] += 1; return lookup(value[0], value[1])
        if kind == 'range':
            pos[0] += 1; return lookup_range(*value)
        if kind == 'func':
            pos[0] += 1
            args = []
            if peek('rp') is None:
                while True:
                    args.append(expression())
                    nxt = peek()
                    if nxt is None: raise _XLFormulaError('fonction non fermée')
                    if nxt[0] == 'sep': pos[0] += 1; continue
                    if nxt[0] == 'rp': break
                    raise _XLFormulaError('argument inattendu')
            if peek('rp') is None: raise _XLFormulaError('fonction non fermée')
            pos[0] += 1
            return _x_formula_func(value, args)
        raise _XLFormulaError('expression non prise en charge')

    def unary():
        tok = peek('op')
        if tok is not None and tok[1] == '-':
            pos[0] += 1; return -_x_formula_num(unary())
        if tok is not None and tok[1] == '+':
            pos[0] += 1; return _x_formula_num(unary())
        return atom()

    def product():
        value = unary()
        while True:
            tok = peek('op')
            if tok is None or tok[1] not in '*/': return value
            pos[0] += 1
            right = _x_formula_num(unary())
            if tok[1] == '*': value = _x_formula_num(value) * right
            else:
                if right == 0: raise _XLFormulaError('division par zéro')
                value = _x_formula_num(value) / right

    def expression():
        value = product()
        while True:
            tok = peek('op')
            if tok is None or tok[1] not in '+-': return value
            pos[0] += 1
            right = _x_formula_num(product())
            value = _x_formula_num(value) + right if tok[1] == '+' else _x_formula_num(value) - right

    result = expression()
    if pos[0] != len(toks): raise _XLFormulaError('formule non prise en charge')
    if isinstance(result, list): raise _XLFormulaError('plage utilisée comme valeur')
    return result


def _x_cell_raw(el, shared):
    """(valeur, formule, formule partagée) d'une cellule <c> telle qu'écrite dans le fichier.

    La valeur est celle mise en cache par le logiciel qui a produit le classeur :
    elle peut manquer (fichier écrit par un générateur, calculs non enregistrés).
    """
    kind = el.get('t', 'n')
    text = formula = shared_f = is_el = None
    for child in el:
        local = _x_local(child)
        if local == 'v': text = child.text
        elif local == 'is': is_el = child
        elif local == 'f':
            formula = child.text or None
            if (child.get('t') or '') == 'shared':
                shared_f = (child.get('si') or '0', formula, child.get('ref') or '')
    if kind == 's':
        try: value = shared[int(text)]
        except (TypeError, ValueError, IndexError): value = None
    elif kind == 'inlineStr' or is_el is not None:
        value = _x_rich_text(is_el) if is_el is not None else None
    elif text is None:
        value = None
    elif kind in ('str', 'e'):
        value = text
    elif kind == 'b':
        value = text.strip().lower() in ('1', 'true')
    elif kind == 'd':
        try: value = dt.datetime.fromisoformat(text.replace('Z', '+00:00')).date()
        except ValueError:
            try: value = dt.date.fromisoformat(text[:10])
            except ValueError: value = None
    else:
        try: value = float(text)
        except ValueError: value = text
    return value, formula, shared_f


def _x_cell_out(value, style_idx, date_styles, epoch):
    """Convertit une valeur brute : une série numérique au format date devient une date."""
    if isinstance(value, float) and style_idx is not None and style_idx in date_styles and 1000 <= value <= 3000000:
        try: return epoch + dt.timedelta(days=int(value))
        except (OverflowError, ValueError): return None
    return value


def _x_sheet_rows(zf, path, shared, date_styles, epoch, border_styles=None, warn=None,
                  sheet_name=None, max_rows=None):
    """Parcourt une feuille : yield (n° de ligne, {colonne: valeur}, {colonnes bordées}).

    Un trou de numérotation devient une ligne vide. Les formules sont lues : la
    valeur en cache est utilisée quand elle existe, sinon la formule est
    recalculée (sommes, références, opérations simples). Une formule illisible
    est signalée : aucun montant ne disparaît en silence.
    """
    border_any = (border_styles or {}).get('any') or set()
    row_order, buffered, col_styles = [], {}, {}
    with zf.open(path) as stream:
        for event, el in ET.iterparse(stream, events=('start', 'end')):
            if event != 'end': continue
            local = _x_local(el)
            if local == 'col':
                st = el.get('style')
                if st and st.isdigit():
                    try:
                        cmin = max(1, int(el.get('min', '1')))
                        cmax = min(256, int(el.get('max', str(cmin))))
                        for ci in range(cmin - 1, cmax): col_styles[ci] = int(st)
                    except ValueError:
                        pass
                el.clear()
            elif local == 'c':
                col = _x_col_ref(el.get('r'))
                if col is None: col = (max(buffered) + 1) if buffered else 0
                value, formula, shared_f = _x_cell_raw(el, shared)
                style = el.get('s')
                sidx = int(style) if (style is not None and style.isdigit()) else col_styles.get(col)
                el.clear()
                if formula is None and not _x_present(value): continue
                buffered[col] = (value, formula, shared_f, sidx)
            elif local == 'row':
                try: num = int(el.get('r'))
                except (TypeError, ValueError): num = (row_order[-1][0] + 1) if row_order else 1
                el.clear()
                if row_order and num > row_order[-1][0] + 1:
                    row_order.append((row_order[-1][0] + 1, {}))
                row_order.append((num, buffered))
                buffered = {}
                if max_rows and len(row_order) >= max_rows: break

    rows_by_num = {}
    for num, cells in row_order: rows_by_num[num] = cells
    has_formula = any(cell[1] or cell[2] for cells in rows_by_num.values() for cell in cells.values())

    stats = {'calc': 0, 'failed': 0, 'first': None}
    if has_formula:
        shared_master = {}
        for num, cells in row_order:
            for col, cell in cells.items():
                if cell[2] and cell[2][1]:
                    shared_master[cell[2][0]] = (cell[2][1], num, col)
        resolved, busy = {}, set()

        def is_formula(cell):
            return cell[1] is not None or (cell[2] is not None and cell[2][1] is None and cell[2][0] in shared_master)

        def value_at(row, col):
            cell = rows_by_num.get(row, {}).get(col)
            if cell is None: return None
            if not is_formula(cell): return cell[0]
            return resolve(row, col)

        def range_at(r1, c1, r2, c2):
            if abs(r2 - r1) > 100000 or abs(c2 - c1) > 256: raise _XLFormulaError('plage trop grande')
            out = []
            for r in range(min(r1, r2), max(r1, r2) + 1):
                for c in range(min(c1, c2), max(c1, c2) + 1):
                    out.append(value_at(r, c))
                    if len(out) > 20000: raise _XLFormulaError('plage trop grande')
            return out

        def resolve(row, col):
            key = (row, col)
            if key in resolved: return resolved[key]
            cell = rows_by_num.get(row, {}).get(col)
            if cell is None: return None
            value, formula, shared_f = cell[0], cell[1], cell[2]
            if formula is None and shared_f is not None:
                master = shared_master.get(shared_f[0])
                if master is None: raise _XLFormulaError('formule partagée sans modèle')
                formula = _x_shift_formula(master[0], row - master[1], col - master[2])
            if formula is None or value is not None:
                resolved[key] = value
                return value
            if key in busy: raise _XLFormulaError('référence circulaire')
            busy.add(key)
            try:
                out = _x_eval_formula(formula, value_at, range_at)
                if out is not None: stats['calc'] += 1
            except _XLFormulaError as exc:
                stats['failed'] += 1
                if stats['first'] is None: stats['first'] = (row, col, formula, str(exc))
                out = None
            except (ArithmeticError, TypeError, ValueError) as exc:
                stats['failed'] += 1
                if stats['first'] is None: stats['first'] = (row, col, formula, str(exc)[:60])
                out = None
            finally:
                busy.discard(key)
            resolved[key] = out
            return out
    else:
        def is_formula(cell): return False
        def resolve(row, col): return None

    for num, cells in row_order:
        out_cells, bordered = {}, set()
        for col in sorted(cells):
            cell = cells[col]
            value = resolve(num, col) if is_formula(cell) else cell[0]
            style_idx = cell[3] if cell[3] is not None else 0
            if border_any and style_idx in border_any: bordered.add(col)
            value = _x_cell_out(value, cell[3], date_styles, epoch)
            if value is not None: out_cells[col] = value
        yield num, out_cells, bordered

    if warn is not None and (stats['calc'] or stats['failed']):
        label = sheet_name or str(path).rsplit('/', 1)[-1]
        if stats['failed']:
            row, col, formula, reason = stats['first']
            others = (' (+ %d autre(s))' % (stats['failed'] - 1)) if stats['failed'] > 1 else ''
            warn('⛔ Feuille « ' + label + ' », cellule ' + _x_col_letter(col) + str(row) + others
                 + ' : la formule « ' + str(formula)[:60] + ' » n’a pas de résultat enregistré et ne peut'
                 + ' pas être recalculée (' + reason + '). Le montant de cette cellule n’a pas été importé.'
                 + ' → Ouvrez le classeur dans Excel, laissez-le recalculer, enregistrez, puis réimportez.')
        if stats['calc']:
            warn('ℹ Feuille « ' + label + ' » : ' + str(stats['calc'])
                 + ' cellule(s) recalculées à l’import (le classeur n’avait pas leur valeur enregistrée).')


def _x_orphan(cells, epoch, default_year=None):
    """Une ligne qui ressemble à des données mais sans en-tête de tableau (jamais de perte silencieuse)."""
    date_cell = cells.get(0)
    if not _x_present(date_cell) or _x_date(date_cell, epoch, default_year) is None: return False
    for col in (2, 3):
        value = cells.get(col)
        if _x_present(value):
            try:
                if _x_amount(value) is not None: return True
            except ValueError:
                pass
    return False


def _x_subtitle_stem(text):
    s = _x_norm(text)
    s = re.sub(r'\b(19\d\d|20\d\d)\b', '', s)
    return ' '.join(s.split())


def _x_pick_sci_title(titles, current_group, sources, state):
    """Choisit le nom de la SCI parmi les lignes de titre précédant un tableau."""
    cleaned = []
    for t in titles:
        s = ' '.join(str(t).split())
        if not s: continue
        if _x_is_balance_label(s):
            # « Bilan 2024 · SCI THEMA » : le nom de la société est conservé.
            s = _x_strip_control_prefix(s)
            if _x_is_balance_label(s): continue
        if _x_is_summary_title(s): continue
        cleaned.append(s)
    if not cleaned:
        return None, []
    non_period = [s for s in cleaned if not _XL_PERIOD_SUBTITLE_RE.match(_x_norm(s))]
    if not non_period:
        return None, []
    known_stems = state.get('subtitle_stems', set())
    if len(non_period) == 1 and (current_group is not None or len(sources) == 1):
        stem = _x_subtitle_stem(non_period[0])
        if stem and stem in known_stems:
            return None, []
    primary_idx = 0
    entity_re = re.compile(r'\b(?:sci|societe|sarl|sas|scp|scpi|gfa|indivision)\b')
    if len(non_period) > 1 and not entity_re.search(_x_norm(non_period[0])):
        for idx_cand, cand in enumerate(non_period[1:], 1):
            if entity_re.search(_x_norm(cand)):
                primary_idx = idx_cand
                break
    primary = non_period[primary_idx]
    sub_stems = [_x_subtitle_stem(s) for i, s in enumerate(non_period) if i != primary_idx and _x_subtitle_stem(s)]
    return primary, sub_stems


def _x_scan_sheet(sheet_name, rows, sources, records, warn, epoch, state, synthetic=False):
    """Détecte les tableaux d'une feuille et en extrait mouvements et contrôles.

    `synthetic` marque une feuille de synthèse (« Synthèse », « Récapitulatif »,
    « Tableau de bord ») : ses montants sont des agrégats déjà présents dans les
    feuilles de détail. Ils sont comptés et signalés, jamais importés : lus comme
    des opérations, ils créaient une SCI fantôme ou doublaient ceux d'une SCI
    réelle, sans le moindre avertissement.
    """
    row_list = list(rows)
    recap_debit = recap_credit = 0.0
    recap_rows = 0
    table_recap = bool(synthetic)
    titles = []
    columns = None
    header_names = {}
    group = None
    table_no = 0
    table_end = None         # index de fin d'un tableau encadré par des bordures
    closed = False           # un tableau s'est terminé : les lignes suivantes sont hors tableau
    previous_row = {}        # dernière ligne de texte : en-tête sur deux lignes
    outside = []             # lignes situées hors du tableau (jamais importées)
    summary_ignored = 0      # lignes de synthèse (totaux, cumuls) écartées
    amount_notes = []        # montants écrits « 1.234 » lus comme 1 234
    anchor = None            # dernier solde de contrôle connu
    anchor_date = None       # date explicite de cette ancre (None si déduite)
    seg_debit = seg_credit = 0.0     # sommes depuis le dernier contrôle (tout type)
    run_debit = run_credit = 0.0     # sommes depuis le dernier solde
    table_debit = table_credit = 0.0 # sommes cumulées du tableau courant
    sheet_group_has_moves = set()
    last_date = None

    def loc(rn, msg): return 'ligne ' + str(rn) + ' : ' + msg

    def wloc(rn): return 'Feuille « ' + sheet_name + ' », ligne ' + str(rn) + ' : '

    def cell(cells, kind):
        col = columns.get(kind) if columns else None
        return cells.get(col) if col is not None else None

    def col_desc(kind, default_label):
        col = columns.get(kind) if columns else None
        if col is None: return default_label
        hname = header_names.get(kind) or default_label
        return 'colonne ' + _x_col_letter(col) + ' (« ' + hname + ' »)'

    def as_text(value):
        if value is None: return ''
        if isinstance(value, float) and value == int(value) and abs(value) < 1e15: return str(int(value))
        return str(value).strip()

    def source_key(title):
        name = ' '.join(str(title).split())[:300]
        m_yr = re.match(r'^(.+?)\s*(?:[\-–—·•]\s*|\s+)(?:annee\s+|exercice\s+)?(19\d\d|20\d\d)$', name, re.I)
        if m_yr:
            base_cand = m_yr.group(1).strip()
            norm_cand = _x_norm(base_cand)
            if re.search(r'\b(?:sci|societe|sarl|sas|scp|scpi|gfa|indivision)\b', norm_cand) or any(
                _x_norm(s.get('name', '')) == norm_cand for s in sources.values()
            ):
                name = base_cand
        key = 'xlsx_' + hashlib.sha256(name.lower().translate(_XL_ACCENTS).encode()).hexdigest()[:16]
        if key not in sources: sources[key] = {'id': key, 'name': name}
        return key

    # Pré-analyse de l'année de référence de la feuille (nom de l'onglet ou titre de tableau sur la page).
    context_year = _x_find_year(sheet_name)
    if context_year is None:
        for _rn, _cells, _brd in row_list:
            if not _cells or _x_header_kinds(_cells): continue
            for _v in _cells.values():
                if isinstance(_v, str):
                    yr = _x_find_year(_v)
                    if yr is not None:
                        context_year = yr
                        break
                elif isinstance(_v, (dt.date, dt.datetime)):
                    context_year = _v.year
                    break
            if context_year is not None:
                break

    def bounded_end(start, relevant):
        """Fin du bloc encadré par des bordures (None si le classeur n'en dessine pas).

        Un tableau bancaire est encadré : la dernière ligne bordée termine les
        opérations. La détection n'est retenue que si au moins trois lignes sont
        bordées, faute de quoi un encadrement « extérieur » ferait perdre la fin
        du tableau.
        """
        last, count = None, (1 if (row_list[start][2] & relevant) else 0)
        for j in range(start + 1, len(row_list)):
            _rn, cells_j, brd_j = row_list[j]
            if not cells_j: continue
            if _x_header_kinds(cells_j): break
            if brd_j and (brd_j & relevant):
                last = j
                count += 1
        return (last + 1) if (count >= 3 and last is not None) else None

    for idx, (rn, cells, bordered) in enumerate(row_list):
        if cells is None: cells = {}
        bordered = bordered or set()
        try:
            if not any(_x_present(v) for v in cells.values()):
                continue

            if table_end is not None and idx >= table_end:
                # Après la dernière ligne bordée : synthèses, notes, récapitulatifs.
                # Les colonnes restent connues pour reconnaître un solde de clôture.
                table_end = None
                closed = True

            kinds = _x_header_kinds(cells)
            header_cells = cells
            if kinds is None:
                merged_header = _x_header_merge(previous_row, cells)
                if merged_header is not None:
                    kinds = _x_header_kinds(merged_header)
                    header_cells = merged_header
            if kinds:
                columns = kinds
                header_names = {k: as_text(header_cells.get(c)) for k, c in kinds.items()}
                table_end = bounded_end(idx, set(kinds.values()))
                closed = False
                table_no += 1
                state['tables'] += 1
                # Un tableau dont les seuls titres sont « Récapitulatif général »,
                # « Synthèse »… n'est pas un relevé : aucun mouvement n'en sort.
                table_recap = bool(synthetic) or any(_x_is_summary_title(x) for x in titles)
                sci_title, sub_stems = _x_pick_sci_title(titles, group, sources, state)
                for st in sub_stems:
                    state.setdefault('subtitle_stems', set()).add(st)
                prev_group = group
                if sci_title:
                    group = source_key(sci_title)
                elif group is None:
                    sname = (sheet_name or '').strip()
                    if _XL_YEAR_ONLY.match(_x_norm(sname)) and len(sources) == 1:
                        group = next(iter(sources))
                    else:
                        base = sname if sname and not _XL_GENERIC_SHEET.match(sname) and not _XL_YEAR_ONLY.match(_x_norm(sname)) else ''
                        group = source_key(base or 'Tableau ' + str(table_no) + ' · ' + (sname or 'sans nom'))
                for t_line in titles:
                    yr = _x_find_year(t_line)
                    if yr is not None: context_year = yr
                titles = []
                if group != prev_group:
                    anchor = None
                    run_debit = run_credit = 0.0
                # Même SCI sur une autre feuille : le dernier solde connu et les
                # mouvements depuis ce solde servent au contrôle de la ligne
                # suivante, même après un changement d'onglet. Sans cela, deux
                # comptes bancaires d'une même SCI passaient inaperçus.
                saved = (state.get('anchor') or {}).get(group)
                if saved and saved[0] and anchor is None:
                    anchor, run_debit, run_credit = saved[1], saved[2], saved[3]
                seg_debit = seg_credit = 0.0
                table_debit = table_credit = 0.0
                previous_row = cells
                continue

            if columns is None:
                parts = [as_text(cells[c]) for c in sorted(cells)]
                text = ' · '.join(p for p in parts if p)
                if closed:
                    # Hors du tableau : jamais une opération, jamais une erreur.
                    outside.append((rn, text))
                    continue
                if _x_orphan(cells, epoch, context_year):
                    raise ValueError(loc(rn, 'données sans ligne d’en-tête Date / Libellé / Débit / Crédit'
                                         + (' (« ' + text[:80] + ' »).' if text else '.')))
                if text:
                    titles.append(text)
                    previous_row = cells
                    yr = _x_find_year(text)
                    if yr is not None and context_year is None: context_year = yr
                continue

            # --- mode données (un en-tête de tableau est actif sur la feuille) ---
            relevant_cols = set(columns.values())
            if not any(_x_present(cells.get(c)) for c in relevant_cols):
                continue

            if table_recap:
                # Feuille ou tableau de synthèse : on compte, on signale, on n'importe pas.
                def _safe(kind):
                    col = columns.get(kind)
                    if col is None: return None
                    try: return _x_amount(cells.get(col), zero_dash=False)
                    except ValueError: return None
                _debit, _credit, _amount = _safe('debit'), _safe('credit'), _safe('amount')
                if _debit is not None: recap_debit += abs(_debit)
                if _credit is not None: recap_credit += abs(_credit)
                if _amount is not None:
                    if _amount < 0: recap_debit += abs(_amount)
                    else: recap_credit += abs(_amount)
                if _debit is not None or _credit is not None or _amount is not None:
                    recap_rows += 1
                continue

            raw_date = cell(cells, 'date')
            label = as_text(cell(cells, 'label'))
            raw_debit = cell(cells, 'debit')
            raw_credit = cell(cells, 'credit')
            raw_solde = cell(cells, 'solde')
            raw_amount = cell(cells, 'amount')
            raw_sens = cell(cells, 'sens')
            amount_only = (columns.get('amount') is not None
                           and columns.get('debit') is None and columns.get('credit') is None)

            if closed and not (_x_present(raw_solde) and not _x_present(raw_debit)
                               and not _x_present(raw_credit) and not _x_present(raw_amount)):
                # Hors tableau : seule une ligne de solde reste un contrôle utile.
                text = ' · '.join(as_text(cells[c]) for c in sorted(cells) if _x_present(cells[c]))
                outside.append((rn, text))
                continue

            # Si un intitulé « Solde ... » ou « Total ... » a été saisi dans la colonne Date, Débit ou Crédit :
            if not label and isinstance(raw_date, str) and _x_is_balance_label(raw_date):
                label = as_text(raw_date)
                raw_date = None
            if not label and isinstance(raw_debit, str) and _x_is_balance_label(raw_debit):
                label = as_text(raw_debit)
                raw_debit = None
            if not label and isinstance(raw_credit, str) and _x_is_balance_label(raw_credit):
                label = as_text(raw_credit)
                raw_credit = None

            def parse_col_amount(val, kind, required, zero_dash=False):
                if not _x_present(val): return None
                try:
                    return _x_amount(val, zero_dash=zero_dash, notes=amount_notes)
                except ValueError as e:
                    if required:
                        raise ValueError(loc(rn, col_desc(kind, kind) + ' : ' + str(e)
                                             + (' (ligne « ' + label[:50] + ' »)' if label else '')))
                    warn('⚠ ' + wloc(rn) + col_desc(kind, kind) + ' : ' + str(e) + '. Montant ignoré.'
                         + ' → Corrigez cette cellule dans le classeur.')
                    return None

            has_any_amount_cell = any(_x_present(v) for v in (raw_debit, raw_credit, raw_solde, raw_amount))
            date_probe = _x_date(raw_date, epoch, context_year) if _x_present(raw_date) else None

            # Ligne de texte sans montant et sans date (ex. titre d'un nouveau tableau, ligne « Solde » vide
            # ou marqueur de fin de tableau « Récapitulatif », « Total des dépenses »…).
            if not has_any_amount_cell and date_probe is None:
                if _x_is_balance_label(label) or (isinstance(raw_date, str) and _x_is_balance_label(raw_date)):
                    continue
                parts = [as_text(cells[c]) for c in sorted(cells) if c in relevant_cols and _x_present(cells.get(c))]
                text = ' · '.join(p for p in parts if p)
                if text and (_x_footer_label(text) or (isinstance(raw_date, str) and _x_footer_label(raw_date))):
                    # « Total janvier », « Récapitulatif »… : fin du tableau si aucune
                    # opération datée ne suit (sinon c'est un simple intertitre).
                    dated_next = False
                    for _k in range(idx + 1, min(idx + 6, len(row_list))):
                        _c = row_list[_k][1]
                        if not _c: continue
                        _d = _c.get(columns.get('date'))
                        if _x_present(_d) and _x_date(_d, epoch, context_year) is not None:
                            dated_next = True
                            break
                    if not dated_next or _x_footer_label(text, strong=True):
                        closed = True
                        outside.append((rn, text))
                        continue
                if text:
                    titles.append(text)
                    previous_row = cells
                    yr = _x_find_year(text)
                    if yr is not None: context_year = yr
                continue

            debit = parse_col_amount(raw_debit, 'debit', True, zero_dash=False)
            credit = parse_col_amount(raw_credit, 'credit', True, zero_dash=False)
            solde = parse_col_amount(raw_solde, 'solde', False, zero_dash=True)

            # Colonne unique « Montant » : le sens vient de la colonne « Sens »,
            # sinon du signe (un montant négatif est une dépense).
            if amount_only and _x_present(raw_amount):
                amount = parse_col_amount(raw_amount, 'amount', True, zero_dash=False)
                if amount is not None:
                    sens = _x_sens_kind(raw_sens)
                    if sens is None and _x_present(raw_sens):
                        raise ValueError(loc(rn, col_desc('sens', 'Sens') + ' : sens illisible « '
                                             + as_text(raw_sens)[:40] + ' » (attendu : Débit ou Crédit)'
                                             + (' pour « ' + label[:50] + ' ».' if label else '.')))
                    if sens is None:
                        sens = 'debit' if amount < 0 else 'credit'
                    if sens == 'debit': debit = abs(amount)
                    else: credit = abs(amount)

            if debit == 0.0 and credit is not None and credit != 0.0:
                debit = None
            elif credit == 0.0 and debit is not None and debit != 0.0:
                credit = None
            elif debit == 0.0 and credit == 0.0 and solde is None and not _x_balance_label_kind(label):
                debit = credit = None

            # Une ligne n'est un contrôle que si son intitulé est un intitulé de
            # contrôle « pur » (« Solde au 31/01 », « Total débit »…) ou si elle
            # ne porte qu'un solde. « Total travaux », « Report charges » ou
            # « Solde notaire » restent des opérations : elles ne doivent plus
            # disparaître de l'import.
            balance_kind = _x_balance_label_kind(label)
            summary_row = _x_summary_label(label)
            has_one_amount = (debit is not None) != (credit is not None)
            looks_like_operation = bool(label) and date_probe is not None and solde is None and has_one_amount
            is_balance_row = (
                (balance_kind is not None and not looks_like_operation)
                or (debit is None and credit is None and solde is not None)
                or (not label and debit is not None and credit is not None)
                or (summary_row and solde is not None and not looks_like_operation)
            )
            if summary_row and not is_balance_row:
                # « Total des dépenses », « Cumul annuel » : ligne de synthèse, pas
                # une opération. Elle était auparavant importée comme un mouvement,
                # ce qui gonflait le solde de la SCI.
                checked = False
                if debit is not None and round(debit, 2) != round(seg_debit, 2) and round(debit, 2) != round(table_debit, 2):
                    warn('⚠ ' + wloc(rn) + 'total annoncé ' + _x_eur(debit) + ' en débit, ' + _x_eur(seg_debit)
                         + ' calculé sur les lignes ci-dessus. Ligne de synthèse non importée.'
                         + ' → Vérifiez ce total dans le classeur.')
                    checked = True
                if credit is not None and round(credit, 2) != round(seg_credit, 2) and round(credit, 2) != round(table_credit, 2):
                    warn('⚠ ' + wloc(rn) + 'total annoncé ' + _x_eur(credit) + ' en crédit, ' + _x_eur(seg_credit)
                         + ' calculé sur les lignes ci-dessus. Ligne de synthèse non importée.'
                         + ' → Vérifiez ce total dans le classeur.')
                    checked = True
                summary_ignored += 1
                if not checked:
                    state['ignored_summary'] = state.get('ignored_summary', 0) + 1
                continue

            if is_balance_row:
                if debit is None and credit is None and solde is None:
                    continue
                is_tot_keyword = bool(re.match(r'^(?:totaux|total|sous[\s\-]*total|cumul)\b', _x_norm(label)))
                if balance_kind and not is_tot_keyword and solde is None:
                    if credit is not None and debit is None:
                        solde = credit
                        credit = None
                    elif debit is not None and credit is None:
                        solde = -abs(debit)
                        debit = None
                date_val = date_probe
                if date_val is None and _x_present(raw_date):
                    date_val = _x_extract_date_from_text(as_text(raw_date), epoch, context_year)
                if date_val is None and label:
                    date_val = _x_extract_date_from_text(label, epoch, context_year)
                has_explicit_date = date_val is not None
                if date_val is None:
                    date_val = last_date or dt.date(context_year or 2000, 1, 1)
                else:
                    last_date = date_val
                    if context_year is None: context_year = date_val.year

                check_totals = (not label) or is_tot_keyword
                if check_totals and (debit is not None or credit is not None) and solde is None:
                    warn('ℹ ' + wloc(rn) + 'ligne de contrôle sans solde : totaux vérifiés, solde non actualisé.')
                if check_totals and debit is not None:
                    if round(seg_debit, 2) != round(debit, 2) and round(table_debit, 2) != round(debit, 2):
                        warn('⚠ ' + wloc(rn) + 'total débit annoncé ' + _x_eur(debit) + ', ' + _x_eur(seg_debit)
                             + ' calculé sur les lignes ci-dessus. → Vérifiez ce total dans le classeur.')
                if check_totals and credit is not None:
                    if round(seg_credit, 2) != round(credit, 2) and round(table_credit, 2) != round(credit, 2):
                        warn('⚠ ' + wloc(rn) + 'total crédit annoncé ' + _x_eur(credit) + ', ' + _x_eur(seg_credit)
                             + ' calculé sur les lignes ci-dessus. → Vérifiez ce total dans le classeur.')
                if solde is not None:
                    if _x_is_debit_balance_label(label) and solde > 0:
                        if anchor is not None and round(anchor + run_credit - run_debit, 2) == round(-solde, 2):
                            solde = -solde
                        elif anchor is None:
                            solde = -solde
                    if anchor is not None:
                        expected = round(anchor + run_credit - run_debit, 2)
                        if expected != round(solde, 2):
                            warn('⛔ ' + wloc(rn) + 'solde attendu ' + _x_eur(expected) + ' au '
                                 + date_val.strftime('%d/%m/%Y') + ', trouvé ' + _x_eur(solde) + ' (écart '
                                 + _x_eur(round(solde - expected, 2)) + '). → Une opération manque sur les lignes'
                                 + ' précédentes, ou son montant diffère : comparez avec le relevé.')
                        state.setdefault('checked', {}).setdefault(group, set()).add(date_val.isoformat())
                    if group not in sheet_group_has_moves:
                        state.setdefault('openings', {}).setdefault(group, []).append(
                            (date_val.isoformat(), round(solde, 2), has_explicit_date)
                        )
                    if group not in state['opening'] and group not in state['movements']:
                        state['opening'].add(group)
                        src = sources.get(group)
                        if src is not None and 'opening' not in src and round(solde, 2) != 0:
                            src['opening'] = round(solde, 2)
                            src['opening_date'] = date_val.isoformat()
                    # Toutes les ancres du relevé (début et fin de mois) sont
                    # conservées : elles servent au contrôle de la colonne
                    # Solde et à la déduction du solde d'ouverture.
                    state.setdefault('balances', {}).setdefault(group, []).append(
                        (date_val.isoformat(), round(solde, 2))
                    )
                    anchor = solde
                    anchor_date = date_val if has_explicit_date else None
                    run_debit = run_credit = 0.0
                seg_debit = seg_credit = 0.0
                continue

            # --- Ligne d'opération (mouvement) ---
            if not _x_present(raw_date):
                raise ValueError(loc(rn, col_desc('date', 'Date') + ' : date manquante sur une ligne de données'
                                     + (' pour « ' + label[:60] + ' »' if label else '')
                                     + ' (une ligne de synthèse sous le tableau doit être séparée par une'
                                     + ' ligne « Total » ou par une ligne vide).'))
            date_val = date_probe
            if date_val is None:
                raise ValueError(loc(rn, col_desc('date', 'Date') + ' : date illisible : « ' + as_text(raw_date)[:60] + ' »'
                                     + (' pour « ' + label[:50] + ' »' if label else '')
                                     + ' (format attendu : JJ/MM/AAAA).'))

            last_date = date_val
            if context_year is None: context_year = date_val.year
            has_amount = debit is not None or credit is not None

            if not label and has_amount:
                # Date + montant sans libellé : c'est une opération, pas un
                # contrôle. Elle était auparavant ignorée silencieusement.
                label = 'Opération sans libellé'
            if label and has_amount:
                if debit is not None and credit is not None:
                    raise ValueError(loc(rn, 'montant à la fois en débit et en crédit (' + _x_eur(debit)
                                         + ' / ' + _x_eur(credit) + ') pour « ' + label[:50] + ' ».'))
                raw = debit if debit is not None else credit
                direction = 'Dépense' if debit is not None else 'Recette'
                if raw < 0:
                    direction = 'Recette' if direction == 'Dépense' else 'Dépense'
                    warn('⚠ ' + wloc(rn) + 'montant négatif (' + _x_eur(raw) + ') enregistré en '
                         + direction + '. → Vérifiez le sens de cette ligne.')
                d = {'date': date_val.isoformat(), 'label': label, 'direction': direction, 'amount': abs(raw)}
                category = as_text(cell(cells, 'category'))
                if category:
                    d['category'] = category
                else:
                    guessed = _x_guess_category(label)
                    if guessed:
                        d['category'] = guessed
                        state.setdefault('guessed_categories', {})[guessed] = \
                            state.setdefault('guessed_categories', {}).get(guessed, 0) + 1
                records.append({**clean('entries', d), 'id': uid(), 'sci': group, 'kind': 'entries'})
                state.setdefault('movements_signed', {}).setdefault(group, []).append(
                    (date_val.isoformat(), round(abs(raw) * (1 if direction == 'Recette' else -1), 2))
                )
                state['movements'].add(group)
                prev_min = state.setdefault('first_move_date', {}).get(group)
                if prev_min is None or d['date'] < prev_min:
                    state['first_move_date'][group] = d['date']
                sheet_group_has_moves.add(group)
                titles = []
                if len(records) > XLSX_MAX_RECORDS:
                    raise ValueError(loc(rn, 'import limité à %s opérations.' % f'{XLSX_MAX_RECORDS:,}'.replace(',', ' ')))
                if debit is not None:
                    seg_debit = round(seg_debit + raw, 2)
                    table_debit = round(table_debit + raw, 2)
                else:
                    seg_credit = round(seg_credit + raw, 2)
                    table_credit = round(table_credit + raw, 2)
                run_debit = round(run_debit + (raw if debit is not None else 0.0), 2)
                run_credit = round(run_credit + (raw if credit is not None else 0.0), 2)
                if solde is None: continue
                # Un relevé peut afficher le solde courant sur chaque ligne sans
                # ligne de solde séparée : ces soldes servent aussi d'ancres, sinon
                # le solde d'ouverture ne pouvait pas être déduit.
                state.setdefault('balances', {}).setdefault(group, []).append(
                    (date_val.isoformat(), round(solde, 2))
                )
                if anchor is not None:
                    expected = round(anchor + run_credit - run_debit, 2)
                    if expected != round(solde, 2):
                        warn('⛔ ' + wloc(rn) + 'solde attendu ' + _x_eur(expected) + ' au '
                             + date_val.strftime('%d/%m/%Y') + ', trouvé ' + _x_eur(solde) + ' (écart '
                             + _x_eur(round(solde - expected, 2)) + '). → Une opération manque sur les lignes'
                             + ' précédentes, ou son montant diffère : comparez avec le relevé.')
                    state.setdefault('checked', {}).setdefault(group, set()).add(date_val.isoformat())
                anchor = solde
                anchor_date = date_val
                seg_debit = seg_credit = 0.0
                run_debit = run_credit = 0.0
                continue

            if label and solde is None:
                warn('⚠ ' + wloc(rn) + 'libellé sans montant (« ' + label[:50] + ' ») : ligne ignorée.'
                     + ' → Ajoutez le montant ou supprimez la ligne.')
                continue
            if not label and not has_amount and solde is None:
                warn('⚠ ' + wloc(rn) + 'date seule (' + date_val.strftime('%d/%m/%Y') + ') : ligne ignorée.'
                     + ' → Ajoutez le libellé et le montant, ou supprimez la ligne.')
                continue
        except ValueError as e:
            raise ValueError(str(e) if str(e).startswith('ligne ') else loc(rn, str(e)))

    if group is not None and anchor is not None:
        state.setdefault('anchor', {})[group] = (anchor_date is not None, anchor, run_debit, run_credit)
    if summary_ignored:
        warn('ℹ Feuille « ' + str(sheet_name) + ' » : ' + str(summary_ignored)
             + ' ligne(s) de synthèse (totaux, cumuls) écartée(s) — ce ne sont pas des opérations.')
    if amount_notes:
        warn('ℹ Feuille « ' + str(sheet_name) + ' » : ' + str(len(amount_notes))
             + ' montant(s) écrits avec un point (« ' + amount_notes[0][:24]
             + ' ») lus comme des milliers (' + _x_eur(_x_amount(amount_notes[0])) + ').')
    if recap_rows:
        total = round(recap_debit + recap_credit, 2)
        warn('⛔ Feuille « ' + str(sheet_name) + ' » : tableau de synthèse — ' + str(recap_rows)
             + ' ligne(s) non importée(s) (' + _x_eur(total) + '). Ces montants sont des totaux,'
             + ' déjà portés par les feuilles de détail. → Si cette feuille est en réalité un relevé,'
             + ' donnez-lui un autre nom que « Synthèse / Récapitulatif / Tableau de bord ».')
    if outside:
        shown = [text[:60] for _rn, text in outside if text][:3]
        detail = (' : « ' + ' », « '.join(shown) + ' »') if shown else ''
        warn('⚠ Feuille « ' + sheet_name + ' » : ' + str(len(outside))
             + ' ligne(s) hors du tableau non importée(s)' + detail + '. Elles ne comptent pas dans le solde.'
             + ' → Si l’une de ces lignes est une vraie opération, placez-la dans le tableau des opérations.')


def _x_finalize_openings(sources, state, warn=None):
    """Détermine le solde d'ouverture et conserve toutes les ancres du relevé.

    Trois cas :
    1. un solde de début de mois précède les mouvements : il est retenu ;
    2. le classeur ne contient que des soldes de fin de mois : l'ouverture est
       déduite (solde de clôture − mouvements de la période) au lieu d'être
       perdue, ce qui sous-évaluait le solde de la SCI ;
    3. aucun solde : la SCI démarre sans solde d'ouverture, tous les mouvements
       comptent (règle de la vue d'ensemble).

    Un récapitulatif de rapprochement est joint à chaque SCI (dernier solde du
    relevé, solde recalculé) : l'écran d'import l'affiche et permet de corriger
    le solde d'ouverture avant d'importer.
    """
    openings_by_group = state.get('openings', {})
    first_moves = state.get('first_move_date', {})
    balances_by_group = state.get('balances', {})
    moves_by_group = state.get('movements_signed', {})
    for gid, src in sources.items():
        anchors = []
        seen = set()
        for day, value in sorted(balances_by_group.get(gid, [])):
            key = (day, round(value, 2))
            if key in seen: continue
            seen.add(key)
            anchors.append((day, round(value, 2)))
        if anchors:
            src['balances'] = [{'date': day, 'value': value, 'kind': 'releve'} for day, value in anchors]
        cands = openings_by_group.get(gid) or []
        first_move = first_moves.get(gid)
        keep = None
        if cands:
            earliest_date, earliest_solde = min(cands, key=lambda x: x[0])[:2]
            if not (first_move and earliest_date > first_move):
                if round(earliest_solde, 2) != 0:
                    keep = (earliest_date, round(earliest_solde, 2), False)
        if keep is None and anchors and first_move:
            # Ouverture déduite du premier solde de clôture connu.
            for day, value in anchors:
                if day < first_move: continue
                total = round(sum(amount for date_, amount in moves_by_group.get(gid, []) if date_ <= day), 2)
                derived = round(value - total, 2)
                if derived:
                    day_before = (dt.date.fromisoformat(first_move) - dt.timedelta(days=1)).isoformat()
                    keep = (day_before, derived, True)
                break
        if keep is None:
            src.pop('opening', None)
            src.pop('opening_date', None)
            src.pop('opening_derived', None)
        else:
            src['opening'] = keep[1]
            src['opening_date'] = keep[0]
            if keep[2]: src['opening_derived'] = True
            else: src.pop('opening_derived', None)
        # Plusieurs soldes de début distincts : soit un report d'une année sur
        # l'autre (le solde repris égale le dernier solde connu), soit deux
        # comptes bancaires différents dont les soldes doivent s'additionner.
        # Le calcul retient le plus ancien ; l'écart est signalé, jamais masqué.
        distinct = sorted({(str(day), round(value, 2)) for day, value, _ in cands})
        if warn is not None and len(distinct) > 1:
            for day, value in distinct[1:]:
                before = [v for d, v in anchors if d <= day]
                if before and abs(before[-1] - value) < 0.005: continue      # report normal
                shown = ' / '.join(dt.date.fromisoformat(d).strftime('%d/%m/%Y') + ' : ' + _x_eur(v)
                                   for d, v in distinct[:4])
                warn('⛔ « ' + str(src.get('name') or gid) + ' » : plusieurs soldes de début distincts ('
                     + shown + '). Le plus ancien est retenu comme solde d’ouverture'
                     + (' (' + _x_eur(keep[1]) + ' au ' + dt.date.fromisoformat(keep[0]).strftime('%d/%m/%Y') + ')' if keep else '')
                     + '. → S’il s’agit de comptes bancaires différents, additionnez leurs soldes'
                     + ' d’ouverture dans l’écran d’import ; sinon, vérifiez la date de reprise.')
                break
        moves = moves_by_group.get(gid, [])
        last = anchors[-1] if anchors else None
        opening_value = keep[1] if keep else 0.0
        opening_day = keep[0] if keep else None
        counted = [amount for day, amount in moves if not opening_day or day >= opening_day]
        calculated = round(opening_value + sum(counted), 2)
        # Solde recalculé à la date du dernier solde du relevé : c'est là que la
        # comparaison avec le classeur a un sens.
        at_last = round(opening_value + sum(amount for day, amount in moves
                                            if (not opening_day or day >= opening_day)
                                            and (not last or day <= last[0])), 2) if last else None
        gap = round(at_last - last[1], 2) if last else None
        state.setdefault('reconcile', {})[gid] = {
            'opening': round(opening_value, 2),
            'opening_date': opening_day,
            'opening_derived': bool(keep and keep[2]),
            'movements': round(sum(counted), 2),
            'calculated': calculated,
            'balance_at_last': at_last,
            'last_balance': last[1] if last else None,
            'last_balance_date': last[0] if last else None,
            'gap': gap,
            'balances': len(anchors),
        }
        checked = state.get('checked', {}).get(gid, set())
        if warn is not None and last and gap is not None and abs(gap) >= 0.005 and last[0] not in checked:
            # Le classeur donne un dernier solde : si le total reconstitué s'en
            # écarte, c'est le signe d'un compte manquant, d'un solde d'ouverture
            # incomplet ou d'une ligne non importée. Jamais silencieux.
            warn('⛔ « ' + str(src.get('name') or gid) + ' » : solde reconstitué ' + _x_eur(at_last)
                 + ', dernier solde du relevé ' + _x_eur(last[1]) + ' au '
                 + dt.date.fromisoformat(last[0]).strftime('%d/%m/%Y') + ' (écart ' + _x_eur(gap) + ').'
                 + ' → Il manque probablement une opération, un compte bancaire, ou une partie'
                 + ' du solde d’ouverture.')


def parse_xlsx(text):
    """Analyse un classeur .xlsx (base64) : plusieurs tableaux, plusieurs feuilles, contrôles de soldes."""
    if not isinstance(text, str) or not text.strip():
        raise ValueError('Fichier Excel absent.')
    try:
        raw = base64.b64decode(text, validate=True)
    except Exception:
        raise ValueError('Fichier Excel illisible (encodage invalide).')
    if not raw: raise ValueError('Fichier Excel vide.')
    try:
        zf = zipfile.ZipFile(io.BytesIO(raw))
        zf.namelist()
    except Exception:
        raise ValueError('Fichier Excel illisible : un classeur .xlsx valide est attendu.')
    with zf:
        if sum(i.file_size for i in zf.infolist()) > 100 * 1024 * 1024:
            raise ValueError('Fichier Excel trop volumineux après décompression (100 Mo maximum).')
        try:
            shared = _x_shared_strings(zf)
            date_styles = _x_styles(zf)
            border_styles = _x_border_styles(zf)
            sheets, epoch = _x_sheets(zf)
        except zipfile.BadZipFile:
            raise ValueError('Fichier Excel illisible : archive endommagée.')
        except ET.ParseError:
            raise ValueError('Fichier Excel illisible (XML invalide).')
        sources = {}
        records = []
        warn_msgs = []
        warn_total = [0]

        def warn(msg):
            warn_total[0] += 1
            if len(warn_msgs) < 30: warn_msgs.append(msg)

        state = {'movements': set(), 'opening': set(), 'tables': 0}
        skipped_sheets = []
        for sheet_name, sheet_path in sheets:
            try:
                synthetic = _x_is_summary_sheet(sheet_name)
                if synthetic: skipped_sheets.append(sheet_name)
                _x_scan_sheet(sheet_name, _x_sheet_rows(zf, sheet_path, shared, date_styles, epoch,
                                                        border_styles=border_styles, warn=warn,
                                                        sheet_name=sheet_name),
                              sources, records, warn, epoch, state, synthetic=synthetic)
            except ValueError as e:
                raise ValueError('Feuille « ' + sheet_name + ' » : ' + str(e))
            except (zipfile.BadZipFile, ET.ParseError):
                raise ValueError('Fichier Excel illisible pendant la lecture de la feuille « ' + sheet_name + ' ».')
        _x_finalize_openings(sources, state, warn)
        if warn_total[0] > len(warn_msgs):
            warn_msgs.append('… et %d autre(s) avertissement(s).' % (warn_total[0] - len(warn_msgs)))
        def _with_warnings(message):
            # Une erreur doit dire quoi faire : les premiers avertissements sont
            # repris dans le message, sinon ils disparaissent avec le refus.
            shown = warn_msgs[:3]
            return message + ((' Pistes : ' + ' | '.join(shown)) if shown else '')

        if not state['tables']:
            extra = (' Feuille(s) de synthèse écartée(s) : ' + ', '.join(skipped_sheets) + '.') if skipped_sheets else ''
            raise ValueError(_with_warnings('Aucun tableau de trésorerie reconnu : les en-têtes « Date », « Libellé »,'
                                            ' « Débit » et « Crédit » sont introuvables.' + extra))
        if not records:
            extra = (' Seule(s) feuille(s) de synthèse lue(s) : ' + ', '.join(skipped_sheets)
                     + '. Importez la feuille du relevé bancaire (détail des opérations).') if skipped_sheets else ''
            raise ValueError(_with_warnings('Aucune opération importable : ' + str(state.get('tables', 0))
                             + ' tableau(x) reconnu(s), mais aucune ligne datée portant un montant en Débit,'
                             + ' en Crédit ou en Montant. → Vérifiez que l’en-tête comporte Date, Libellé et'
                             + ' Débit/Crédit (ou Montant + Sens), puis lisez les avertissements ci-dessous.' + extra))
        if len(records) > XLSX_MAX_RECORDS:
            raise ValueError('Import limité à %s opérations.' % f'{XLSX_MAX_RECORDS:,}'.replace(',', ' '))
        return {'application': 'Dominis', 'version': 1, 'scis': list(sources.values()), 'records': records,
                'warnings': warn_msgs, 'reconcile': state.get('reconcile', {})}


def _parse_tabular_csv(text, delimiter=';'):
    """Analyse un CSV structuré comme un tableau Excel (Titres, Date / Libellé / Débit / Crédit / Solde)."""
    epoch = dt.date(1899, 12, 30)
    raw_rows = []
    reader = csv.reader(io.StringIO(text), delimiter=delimiter)
    for rn, row in enumerate(reader, 1):
        cells = {ci: val.strip() for ci, val in enumerate(row) if val and val.strip()}
        raw_rows.append((rn, cells, set()))
    if not any(_x_header_kinds(c) for _, c, _b in raw_rows if c):
        return None
    sources = {}
    records = []
    warn_msgs = []
    warn_total = [0]

    def warn(msg):
        warn_total[0] += 1
        if len(warn_msgs) < 30: warn_msgs.append(msg)

    state = {'movements': set(), 'opening': set(), 'tables': 0}
    try:
        _x_scan_sheet('CSV', iter(raw_rows), sources, records, warn, epoch, state)
    except ValueError as e:
        raise ValueError('Fichier CSV : ' + str(e))
    _x_finalize_openings(sources, state, warn)
    if warn_total[0] > len(warn_msgs):
        warn_msgs.append('… et %d autre(s) avertissement(s).' % (warn_total[0] - len(warn_msgs)))
    if not state['tables'] or not records:
        raise ValueError('Les tableaux reconnus dans le CSV ne contiennent aucune opération.')
    return {'application': 'Dominis', 'version': 1, 'scis': list(sources.values()), 'records': records,
            'warnings': warn_msgs, 'reconcile': state.get('reconcile', {})}


PDF_PAGE_W, PDF_PAGE_H = 595.28, 841.89
PDF_MARGIN = 46.0
PDF_INK = '#202024'
PDF_MUTED = '#717969'
PDF_LINE = '#dfdfd4'
PDF_GOLD = '#b91c2b'
PDF_GREEN = '#367858'
PDF_RED = '#b45043'
PDF_SOFT = '#f6f4ec'
PDF_HEAD = '#f6e9eb'
PDF_ZEBRA = '#faf9f4'


def _pdf_rgb(h):
    h = str(h or '#252c25').lstrip('#')
    if len(h) != 6:
        h = '252c25'
    try:
        return ' '.join('%.3f' % (int(h[i:i + 2], 16) / 255.0) for i in (0, 2, 4))
    except ValueError:
        return '0.145 0.173 0.145'


PDF_CHAR_MAP = {
    '\u202f': ' ', '\u00a0': ' ', '\u2009': ' ', '\u2007': ' ', '\u2060': '',
    '\u2011': '-', '\u2212': '-', '\u2010': '-', '\u2013': '\u2013', '\u2014': '\u2014',
    '\u2018': "'", '\u2019': '\u2019', '\u201c': '"', '\u201d': '"',
    '\u2026': '\u2026', '\u20ac': '\u20ac',
    # Le contenu est écrit en cp1252 : les caractères absents de cette page de
    # code étaient remplacés par « ? ». On les translittère explicitement.
    '\u2192': '->', '\u2190': '<-', '\u21d2': '=>', '\u21d0': '<=',
    '\u2264': '<=', '\u2265': '>=', '\u2260': '!=', '\u2248': '~',
    '\u2032': "'", '\u2033': '"', '\u2022': '\u2022', '\u00b7': '\u00b7',
}


def _pdf_esc(text):
    out = []
    raw = str(text if text is not None else '')
    for ch in ''.join(PDF_CHAR_MAP.get(c, c) for c in raw):
        if ch in '()\\':
            out.append('\\' + ch)
        elif ch in '\r\n\t':
            out.append(' ')
        else:
            out.append(ch)
    return ''.join(out)


def _pdf_width(text, size, bold=False):
    """Largeur approchée en points, volontairement majorée.

    Les caractères larges (cadratin, points de suspension, guillemets français)
    étaient sous-estimés : un texte tronqué « à la largeur » débordait alors de
    sa colonne, parfois au-delà de la marge de la page. Le facteur final garde
    une marge de sécurité de 2 %.
    """
    narrow = set("il.,:;'!|")
    wide = set('mwMW@')
    total = 0.0
    for ch in str(text or ''):
        if ch == ' ':
            total += 0.278
        elif ch in narrow:
            total += 0.255
        elif ch in wide:
            total += 0.84
        elif ch.isdigit():
            total += 0.556
        elif ch.isupper():
            total += 0.68
        elif ch in '()[]{}':
            total += 0.333
        elif ch in '—…':
            total += 1.0
        elif ch in '«»€':
            total += 0.556
        elif ch in '-–·’':
            total += 0.3
        else:
            total += 0.53
    return total * size * (1.03 if bold else 1.0) * 1.02


def _pdf_wrap(text, size, width, bold=False):
    """Découpe un texte en lignes, en coupant les mots plus larges que la ligne.

    Un mot insécable (référence, adresse sans espace) dépassait sinon de sa
    colonne, parfois au-delà de la marge de la page.
    """
    text = str(text or '').replace('\n', ' ')
    width = max(12.0, float(width))

    def split_long(word):
        parts, cur = [], ''
        for ch in word:
            if cur and _pdf_width(cur + ch, size, bold) > width:
                parts.append(cur)
                cur = ch
            else:
                cur += ch
        if cur:
            parts.append(cur)
        return parts

    lines, cur = [], ''
    for word in text.split(' '):
        if not word:
            continue
        for piece in ([word] if _pdf_width(word, size, bold) <= width else split_long(word)):
            candidate = (cur + ' ' + piece).strip()
            if not cur or _pdf_width(candidate, size, bold) <= width:
                cur = candidate
            else:
                lines.append(cur)
                cur = piece
    if cur:
        lines.append(cur)
    return lines or ['']


def _pdf_clip(text, size, width, bold=False):
    text = str(text or '')
    if _pdf_width(text, size, bold) <= width:
        return text
    out = ''
    for ch in text:
        if _pdf_width(out + ch + '…', size, bold) > width:
            break
        out += ch
    return (out.rstrip() + '…') if out else '…'


def _pdf_money_short(v):
    v = float(v or 0)
    sign = '−' if v < 0 else ''
    v = abs(v)
    if v >= 1000:
        txt = ('%.1f' % (v / 1000.0)).rstrip('0').rstrip('.').replace('.', ',')
        return sign + txt + ' k€'
    return sign + ('%.0f' % v) + ' €'


class PdfAnnualReport:
    def __init__(self, model):
        self.model = model if isinstance(model, dict) else {}
        self.pages = []
        self.ops = []
        self.y = PDF_PAGE_H - PDF_MARGIN
        self.continuation = self._continuation_label()

    def _continuation_label(self):
        title = str(self.model.get('title') or '')
        sub = str(self.model.get('subtitle') or '')
        return (title + ' · ' + sub).strip(' ·')

    @property
    def width(self):
        return PDF_PAGE_W - 2 * PDF_MARGIN

    def new_page(self):
        if self.ops:
            self.pages.append(self.ops)
            self.ops = []
        self.y = PDF_PAGE_H - PDF_MARGIN
        if self.pages:
            self.text(PDF_MARGIN, self.y - 7, str(self.model.get('eyebrow') or 'DOMINIS · SYNTHÈSE ANNUELLE'), 7.5, 'F2', PDF_GOLD)
            self.text(PDF_PAGE_W - PDF_MARGIN, self.y - 7, _pdf_clip(self.continuation, 7.5, 400), 7.5, 'F1', PDF_MUTED, align='right')
            self.y -= 16
            self.rule(PDF_LINE)
            self.y -= 12

    def need(self, height):
        if self.y - height < PDF_MARGIN + 30:
            self.new_page()
            return True
        return False

    def rect(self, x, y, w, h, fill=None, stroke=None, lw=0.6):
        if fill:
            self.ops.append('%s rg' % _pdf_rgb(fill))
        if stroke:
            self.ops.append('%s RG %.2f w' % (_pdf_rgb(stroke), lw))
        self.ops.append('%.2f %.2f %.2f %.2f re' % (x, y, w, h))
        self.ops.append('B' if (fill and stroke) else ('f' if fill else 'S'))

    def line(self, x1, y1, x2, y2, color=PDF_LINE, lw=0.6):
        self.ops.append('%s RG %.2f w' % (_pdf_rgb(color), lw))
        self.ops.append('%.2f %.2f m %.2f %.2f l S' % (x1, y1, x2, y2))

    def rule(self, color=PDF_LINE, lw=0.7):
        self.line(PDF_MARGIN, self.y, PDF_PAGE_W - PDF_MARGIN, self.y, color, lw)

    def text(self, x, y, txt, size=9, font='F1', color=PDF_INK, align='left'):
        txt = str(txt if txt is not None else '')
        if align != 'left':
            w = _pdf_width(txt, size, font == 'F2')
            x = x - w if align == 'right' else x - w / 2.0
        self.ops.append('BT /%s %.2f Tf %s rg 1 0 0 1 %.2f %.2f Tm (%s) Tj ET' % (
            font, size, _pdf_rgb(color), x, y, _pdf_esc(txt)))

    def paragraph(self, txt, size=8.9, color=PDF_MUTED, indent=0.0, leading=11.8):
        for line in _pdf_wrap(txt, size, self.width - indent):
            self.need(leading + 2)
            self.text(PDF_MARGIN + indent, self.y - leading + 3, line, size, 'F1', color)
            self.y -= leading
        self.y -= 3

    def heading(self, title, reserve=0.0):
        # Un titre ne doit jamais rester seul en bas de page : on exige la place
        # du titre, puis celle du premier bloc de contenu annoncée par l'appelant
        # (l'en-tête d'un tableau et ses premières lignes, par exemple).
        self.need(96 + max(0.0, min(150.0, float(reserve or 0))))
        self.y -= 4
        self.rect(PDF_MARGIN, self.y - 12, 3, 12, fill=PDF_GOLD)
        self.text(PDF_MARGIN + 10, self.y - 10, title, 12.5, 'F2', PDF_INK)
        self.y -= 17
        self.rule(PDF_LINE)
        self.y -= 11

    def notice(self, txt, size=8.2):
        if not txt:
            return
        lines = _pdf_wrap(txt, size, self.width - 26)
        h = len(lines) * 11.4 + 18
        self.need(h + 8)
        top = self.y
        self.rect(PDF_MARGIN, top - h, self.width, h, fill=PDF_SOFT, stroke=PDF_LINE)
        self.rect(PDF_MARGIN, top - h, 3, h, fill=PDF_GOLD)
        for i, line in enumerate(lines):
            self.text(PDF_MARGIN + 13, top - 14 - i * 11.4, line, size, 'F1', '#5c6459')
        self.y = top - h - 10

    def kpi_cards(self, items):
        items = [it for it in (items or []) if isinstance(it, dict)][:4]
        if not items:
            return
        gap = 8.0
        w = (self.width - gap * (len(items) - 1)) / len(items)
        h = 54.0
        self.need(h + 10)
        top = self.y
        tones = {'green': PDF_GREEN, 'red': PDF_RED, 'gold': PDF_GOLD}
        for i, item in enumerate(items):
            x = PDF_MARGIN + i * (w + gap)
            self.rect(x, top - h, w, h, fill=PDF_SOFT, stroke=PDF_LINE)
            self.text(x + 10, top - 16, _pdf_clip(item.get('label', ''), 7.2, w - 16), 7.2, 'F2', PDF_MUTED)
            value = str(item.get('value') or '—')
            size = 13.5 if _pdf_width(value, 13.5, True) <= w - 18 else (11.5 if _pdf_width(value, 11.5, True) <= w - 18 else 9.6)
            self.text(x + 10, top - 39, value, size, 'F2', tones.get(str(item.get('tone')), PDF_INK))
        self.y = top - h - 12

    def bar_chart(self, chart):
        labels = [str(x) for x in (chart.get('labels') or [])]
        series = [s for s in (chart.get('series') or []) if isinstance(s, dict)]
        if not labels or not series:
            return
        height = 158.0
        self.need(height + 52)
        top = self.y - 4
        plot_left = PDF_MARGIN + 44
        plot_right = PDF_PAGE_W - PDF_MARGIN
        plot_width = plot_right - plot_left
        bottom = top - height + 26
        plot_h = top - bottom
        values = []
        for s in series:
            for v in (s.get('values') or []):
                try:
                    values.append(max(0.0, float(v)))
                except (TypeError, ValueError):
                    values.append(0.0)
        maxv = max(values) if values else 0.0
        maxv = maxv or 1.0
        # Graduation lisible (0 · 1 k€ · 2 k€ …) plutôt qu'un maximum brut.
        raw = maxv / 4.0
        mag = 10 ** math.floor(math.log10(raw)) if raw > 0 else 1
        step = mag * 10
        for mult in (1, 2, 2.5, 5, 10):
            if mag * mult * 4 >= maxv:
                step = mag * mult
                break
        maxv = step * 4
        for g in range(5):
            y = bottom + plot_h * g / 4.0
            self.line(plot_left, y, plot_right, y, PDF_LINE, 0.4)
            self.text(plot_left - 6, y - 3, _pdf_money_short(maxv * g / 4.0), 6.8, 'F1', PDF_MUTED, align='right')
        group = plot_width / len(labels)
        bar_w = max(3.0, min(11.0, group * 0.26))
        for i, label in enumerate(labels):
            center = plot_left + group * (i + 0.5)
            start = center - (len(series) * bar_w + (len(series) - 1) * 2) / 2.0
            for j, s in enumerate(series):
                try:
                    v = max(0.0, float((s.get('values') or [])[i]))
                except (TypeError, ValueError, IndexError):
                    v = 0.0
                if v <= 0:
                    continue
                bh = max(1.0, plot_h * v / maxv)
                self.rect(start + j * (bar_w + 2), bottom, bar_w, bh, fill=str(s.get('color') or PDF_GOLD))
            self.text(center, bottom - 12, label, 7.2, 'F1', PDF_MUTED, align='center')
        legend_y = bottom - 27
        lx = plot_left
        for s in series:
            self.rect(lx, legend_y, 7, 7, fill=str(s.get('color') or PDF_GOLD))
            self.text(lx + 11, legend_y + 0.5, str(s.get('label') or ''), 7.6, 'F1', PDF_INK)
            lx += 22 + _pdf_width(str(s.get('label') or ''), 7.6)
        self.y = legend_y - 14

    def hbar_chart(self, chart):
        items = [it for it in (chart.get('items') or []) if isinstance(it, dict)]
        if not items:
            self.paragraph('Aucune dépense enregistrée sur l’exercice.')
            return
        row_h = 21.0
        self.need(len(items) * row_h + 12)
        label_w = 132.0
        bar_x = PDF_MARGIN + label_w
        value_w = 74.0
        bar_w = PDF_PAGE_W - PDF_MARGIN - bar_x - value_w - 8
        maxv = max([float(it.get('value') or 0) for it in items] + [1.0])
        top = self.y
        for i, item in enumerate(items):
            y = top - (i + 1) * row_h
            self.text(PDF_MARGIN, y + 6, _pdf_clip(item.get('label', ''), 8.4, label_w - 8), 8.4, 'F1', PDF_INK)
            self.rect(bar_x, y + 2, bar_w, 9, fill='#eeece3')
            w = max(2.0, bar_w * float(item.get('value') or 0) / maxv)
            self.rect(bar_x, y + 2, w, 9, fill=str(item.get('color') or PDF_RED))
            self.text(PDF_PAGE_W - PDF_MARGIN, y + 4, str(item.get('value_label') or _pdf_money_short(item.get('value'))), 8.2, 'F2', PDF_INK, align='right')
        self.y = top - len(items) * row_h - 10

    def table(self, table):
        if not isinstance(table, dict):
            return
        headers = [str(h) for h in (table.get('headers') or [])]
        rows = [[str(c) for c in row] for row in (table.get('rows') or [])]
        if not headers:
            return
        # Un modèle incomplet (moins de largeurs ou d'alignements que de
        # colonnes) ne doit jamais interrompre la génération du dossier : les
        # valeurs manquantes reprennent les réglages par défaut.
        weights = list(table.get('weights') or [])
        weights = [w for w in weights if isinstance(w, (int, float)) and w > 0]
        weights = (weights + [1.0] * len(headers))[:len(headers)]
        aligns = list(table.get('aligns') or [])
        aligns = (aligns + ['left'] * len(headers))[:len(headers)]
        total = sum(weights) or float(len(headers))
        widths = [self.width * float(w) / total for w in weights]
        xpos = []
        x = PDF_MARGIN
        for w in widths:
            xpos.append(x)
            x += w

        def header():
            self.need(26)
            top = self.y
            self.rect(PDF_MARGIN, top - 20, self.width, 20, fill=PDF_HEAD)
            for i, head in enumerate(headers):
                ax = xpos[i] + widths[i] - 6 if aligns[i] == 'right' else xpos[i] + 6
                self.text(ax, top - 13.5, _pdf_clip(head, 7.8, widths[i] - 12), 7.8, 'F2', PDF_INK, align=aligns[i])
            self.y = top - 20

        header()
        for ri, row in enumerate(rows):
            cells = []
            for i in range(len(headers)):
                value = row[i] if i < len(row) else ''
                cells.append(_pdf_wrap(value, 8.3, widths[i] - 12))
            h = max(len(c) for c in cells) * 11.2 + 9
            if self.y - h < PDF_MARGIN + 30:
                self.new_page()
                header()
            top = self.y
            if ri % 2 == 1:
                self.rect(PDF_MARGIN, top - h, self.width, h, fill=PDF_ZEBRA)
            for i, lines in enumerate(cells):
                for li, line in enumerate(lines):
                    ax = xpos[i] + widths[i] - 6 if aligns[i] == 'right' else xpos[i] + 6
                    self.text(ax, top - 12.5 - li * 11.2, line, 8.3, 'F1', PDF_INK, align=aligns[i])
            self.y = top - h
            self.line(PDF_MARGIN, self.y, PDF_PAGE_W - PDF_MARGIN, self.y, PDF_LINE, 0.4)
        self.y -= 9

    def analysis_block(self, analysis):
        for label, key, color in (('Points forts', 'strengths', PDF_GREEN), ('Points de vigilance', 'watch', PDF_RED)):
            items = [str(x) for x in (analysis.get(key) or []) if str(x).strip()]
            if not items:
                continue
            self.need(28)
            self.text(PDF_MARGIN, self.y - 9, label, 8.8, 'F2', color)
            self.y -= 16
            for item in items:
                lines = _pdf_wrap(item, 8.7, self.width - 16)
                h = len(lines) * 11.6 + 3
                self.need(h)
                self.rect(PDF_MARGIN + 1, self.y - 7.5, 4, 4, fill=color)
                for i, line in enumerate(lines):
                    self.text(PDF_MARGIN + 12, self.y - 9 - i * 11.6, line, 8.7, 'F1', PDF_INK)
                self.y -= h
            self.y -= 4
        conclusion = str(analysis.get('conclusion') or '').strip()
        if conclusion:
            lines = _pdf_wrap(conclusion, 8.8, self.width - 26)
            h = len(lines) * 12.0 + 32
            self.need(h)
            top = self.y
            self.rect(PDF_MARGIN, top - h, self.width, h, fill=PDF_SOFT, stroke=PDF_LINE)
            self.rect(PDF_MARGIN, top - h, 3, h, fill=PDF_GOLD)
            self.text(PDF_MARGIN + 13, top - 15, 'En résumé', 8.0, 'F2', PDF_GOLD)
            for i, line in enumerate(lines):
                self.text(PDF_MARGIN + 13, top - 29 - i * 12.0, line, 8.8, 'F1', PDF_INK)
            self.y = top - h - 10

    def draw_header(self):
        model = self.model
        self.text(PDF_MARGIN, self.y - 7, str(model.get('eyebrow') or 'DOMINIS · SYNTHÈSE ANNUELLE'), 8.0, 'F2', PDF_GOLD)
        self.y -= 26
        title = str(model.get('title') or '')
        for line in _pdf_wrap(title, 21, self.width, True)[:2]:
            self.text(PDF_MARGIN, self.y - 16, line, 21, 'F2', PDF_INK)
            self.y -= 25
        subtitle = str(model.get('subtitle') or '')
        if subtitle:
            self.text(PDF_MARGIN, self.y - 11, subtitle, 10.6, 'F1', PDF_GOLD)
            self.y -= 19
        meta = [str(x) for x in (model.get('meta') or []) if str(x).strip()]
        if meta:
            self.text(PDF_MARGIN, self.y - 8, ' · '.join(meta), 8.2, 'F1', PDF_MUTED)
            self.y -= 18
        self.rule(PDF_GOLD, 1.0)
        self.y -= 12
        self.notice(str(model.get('notice') or ''))

    def section(self, sec):
        if not isinstance(sec, dict):
            return
        # Hauteur approximative du premier bloc : elle est réservée avec le
        # titre pour qu'aucun tableau ne commence sur la page suivante.
        table = sec.get('table')
        if isinstance(table, dict):
            probe = 24.0 + 21.0 * min(3, len(table.get('rows') or []))
        elif isinstance(sec.get('analysis'), dict):
            probe = 84.0
        elif sec.get('kpis'):
            probe = 64.0
        elif isinstance(sec.get('chart'), dict):
            probe = 120.0
        elif sec.get('paragraphs'):
            probe = 54.0
        else:
            probe = 0.0
        self.heading(str(sec.get('title') or ''), probe)
        for para in (sec.get('paragraphs') or []):
            if str(para).strip():
                self.paragraph(str(para))
        if sec.get('kpis'):
            self.kpi_cards(sec.get('kpis'))
        chart = sec.get('chart')
        if isinstance(chart, dict):
            if chart.get('type') == 'hbar':
                self.hbar_chart(chart)
            else:
                self.bar_chart(chart)
        if sec.get('table'):
            self.table(sec.get('table'))
        if isinstance(sec.get('analysis'), dict):
            self.analysis_block(sec.get('analysis'))
        if sec.get('note'):
            self.notice(str(sec.get('note')), 7.9)

    def render(self):
        self.draw_header()
        for sec in (self.model.get('sections') or []):
            self.section(sec)

    def build(self):
        if self.ops:
            self.pages.append(self.ops)
            self.ops = []
        if not self.pages:
            self.pages = [[]]
        total = len(self.pages)
        footer_left = _pdf_clip(str(self.model.get('footer') or ('Dominis · Synthèse annuelle · ' + str(self.model.get('title') or ''))), 7.0, 360)
        for i, ops in enumerate(self.pages, 1):
            ops.append('BT /F1 7.0 Tf %s rg 1 0 0 1 %.2f 24 Tm (%s) Tj ET' % (
                _pdf_rgb(PDF_MUTED), PDF_MARGIN, _pdf_esc(footer_left)))
            label = '%d / %d' % (i, total)
            ops.append('BT /F1 7.0 Tf %s rg 1 0 0 1 %.2f 24 Tm (%s) Tj ET' % (
                _pdf_rgb(PDF_MUTED), PDF_PAGE_W - PDF_MARGIN - _pdf_width(label, 7.0), _pdf_esc(label)))

        objects = []

        def add(data):
            objects.append(data)
            return len(objects)

        catalog_id = add(b'')
        pages_id = add(b'')
        font_regular = add(b'<< /Type /Font /Subtype /Type1 /BaseFont /Helvetica /Encoding /WinAnsiEncoding >>')
        font_bold = add(b'<< /Type /Font /Subtype /Type1 /BaseFont /Helvetica-Bold /Encoding /WinAnsiEncoding >>')
        font_italic = add(b'<< /Type /Font /Subtype /Type1 /BaseFont /Helvetica-Oblique /Encoding /WinAnsiEncoding >>')
        page_ids = []
        for ops in self.pages:
            content = '\n'.join(ops).encode('cp1252', 'replace')
            cid = add(b'<< /Length ' + str(len(content)).encode() + b' >>\nstream\n' + content + b'\nendstream')
            resources = ('<< /Type /Page /Parent %d 0 R /MediaBox [0 0 %.2f %.2f] '
                         '/Resources << /Font << /F1 %d 0 R /F2 %d 0 R /F3 %d 0 R >> >> '
                         '/Contents %d 0 R >>' % (
                             pages_id, PDF_PAGE_W, PDF_PAGE_H, font_regular, font_bold, font_italic, cid))
            page_ids.append(add(resources.encode('ascii')))
        objects[catalog_id - 1] = ('<< /Type /Catalog /Pages %d 0 R >>' % pages_id).encode('ascii')
        objects[pages_id - 1] = ('<< /Type /Pages /Count %d /Kids [%s] >>' % (
            len(page_ids), ' '.join('%d 0 R' % p for p in page_ids))).encode('ascii')

        out = bytearray(b'%PDF-1.4\n%\xe2\xe3\xcf\xd3\n')
        offsets = []
        for i, obj in enumerate(objects, 1):
            offsets.append(len(out))
            out += ('%d 0 obj\n' % i).encode('ascii') + obj + b'\nendobj\n'
        xref = len(out)
        out += ('xref\n0 %d\n' % (len(objects) + 1)).encode('ascii')
        out += b'0000000000 65535 f \n'
        for off in offsets:
            out += ('%010d 00000 n \n' % off).encode('ascii')
        out += ('trailer\n<< /Size %d /Root %d 0 R >>\nstartxref\n%d\n%%%%EOF\n' % (
            len(objects) + 1, catalog_id, xref)).encode('ascii')
        return bytes(out), len(self.pages)


def statement_lines(text, page=1):
    """Propositions prudentes : jamais de catégorie devinée ni de ligne ignorée en silence."""
    output=[]; debit_col=credit_col=None
    date_re=re.compile(r'(?<!\d)(\d{2})[/.-](\d{2})[/.-](\d{4}|\d{2})(?!\d)')
    amount_re=re.compile(r'(?<![\w/])[-+−]?(?:\d{1,3}(?:[ \u00a0\u202f]\d{3})+|\d+)[,.]\d{2}(?!\d)')
    for raw in text.splitlines():
        line=raw.strip()
        if not line: continue
        normalized=_x_norm(line)
        if 'debit' in normalized and 'credit' in normalized:
            import unicodedata
            aligned=''.join(ch for ch in unicodedata.normalize('NFKD',raw.lower()) if not unicodedata.combining(ch))
            debit_col=aligned.find('debit');credit_col=aligned.find('credit')
        dates=list(date_re.finditer(raw))
        amounts=[m for m in amount_re.finditer(raw) if not any(m.start()<d.end() and m.end()>d.start() for d in dates)]
        if not dates and not amounts:
            output.append({'source':line,'page':page,'context':True});continue
        warnings=[]; day=''; amount=''; direction=''
        if dates:
            if len(dates)>1: warnings.append('Plusieurs dates : vérifier la date d’opération, distincte de la date de valeur.')
            dd,mm,yyyy=dates[0].groups()
            if len(yyyy)==2: warnings.append('Année à deux chiffres : compléter la date.')
            else:
                try: day=dt.date(int(yyyy),int(mm),int(dd)).isoformat()
                except ValueError: warnings.append('Date invalide.')
        if len(amounts)==1:
            token=amounts[0].group().replace('−','-').replace(',','.')
            amount=abs(float(re.sub(r'\s','',token)))
            if token.startswith('-'): direction='Dépense'
            elif token.startswith('+'): direction='Recette'
            # Les colonnes ne sont utilisées que si leur position est nette.
            elif debit_col is not None and credit_col is not None:
                pos=amounts[0].start(); distances=[abs(pos-debit_col),abs(pos-credit_col)]
                if abs(distances[0]-distances[1])>=5:
                    direction='Dépense' if distances[0]<distances[1] else 'Recette'
                    warnings.append('Sens proposé selon la position dans les colonnes débit/crédit : à vérifier.')
        elif amounts: warnings.append('Plusieurs montants : identifier le montant du mouvement.')
        label=line
        for match in reversed(list(date_re.finditer(label))): label=label[:match.start()]+label[match.end():]
        label=amount_re.sub('',label).strip(' ;|\t')
        if re.search(r'\b(solde|total|totaux|report|cumul)\b',normalized):
            warnings.append('Solde ou total possible : ne pas importer comme mouvement sans vérification.')
        if not day: warnings.append('Date à renseigner.')
        if not amount: warnings.append('Montant à renseigner.')
        if not direction: warnings.append('Débit ou crédit à préciser.')
        warnings.append('Catégorie à choisir ; libellé à vérifier avec le relevé.')
        output.append({'date':day,'label':label,'amount':amount,'direction':direction,'category':'',
                       'source':line,'page':page,'warnings':warnings,'context':False})
    return output



def _x_guess_category(label):
    return ""

LOGO_PNG = base64.b64decode('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')

DOMINIS_CSS = "\n:root{--bg:#101211;--side:#141614;--panel:#191c19;--panel2:#20241f;--line:#2b302a;--text:#edece5;--muted:#92988d;--gold:#c7ad77;--goldbg:#2d2a20;--green:#86bea2;--red:#df8e83;--blue:#849fdb;--shadow:0 24px 90px #0007;--radius:13px;color-scheme:dark}\n:root[data-theme=light]{--bg:#f4f3ee;--side:#eeeee6;--panel:#fffef9;--panel2:#f0f0e8;--line:#dfdfd4;--text:#252c25;--muted:#717969;--gold:#876b35;--goldbg:#eae1cd;--green:#367858;--red:#b45043;--blue:#566db6;--shadow:0 24px 90px #36402c22;color-scheme:light}\n*{box-sizing:border-box}body{margin:0;background:var(--bg);color:var(--text);font-family:Arial,Helvetica,sans-serif;font-size:13px;line-height:1.5}button,input,select,textarea{font:inherit}button,a,input,select,textarea{outline-color:var(--gold)}button,a{ -webkit-tap-highlight-color:transparent}button{cursor:pointer}button{border:1px solid var(--line);color:var(--text);background:var(--panel2);border-radius:7px;padding:9px 13px;display:inline-flex;align-items:center;justify-content:center;gap:8px;transition:background .18s,transform .18s}button:hover{background:var(--line)}button:disabled{opacity:.45;cursor:wait}button.primary{background:var(--gold);border-color:var(--gold);color:#171b15;font-weight:600}button.primary:hover{filter:brightness(1.1)}button.ghost{border-color:transparent;background:transparent}button.danger{color:var(--red)}svg.icon{width:18px;height:18px;fill:none;stroke:currentColor;stroke-width:1.65;stroke-linecap:round;stroke-linejoin:round;flex:none}.small-icon svg{width:15px;height:15px}.icon-only{width:34px;height:34px;padding:7px}.muted{color:var(--muted)}.gold{color:var(--gold)}.green{color:var(--green)}.red{color:var(--red)}h1,h2,h3,p{margin:0}h1{font-family:Georgia,'Times New Roman',serif;font-size:33px;font-weight:400;letter-spacing:-.7px;line-height:1.2}h2{font-size:15px;font-weight:600}h3{font-size:14px;font-weight:600}.eyebrow{font-size:10px;letter-spacing:1.8px;text-transform:uppercase;color:var(--muted);font-weight:600}.sub{font-size:12px;color:var(--muted)}.serif{font-family:Georgia,serif;font-weight:400}.row{display:flex;align-items:center;gap:12px}.between{justify-content:space-between}.wrap{flex-wrap:wrap}.stack{display:flex;flex-direction:column;gap:16px}.gap8{gap:8px}a{color:var(--gold)}\n#sidebar{width:244px;position:fixed;inset:0 auto 0 0;background:var(--side);border-right:1px solid var(--line);display:flex;flex-direction:column;z-index:30;transition:width .3s cubic-bezier(.22,.8,.25,1);overflow:hidden}.brand{height:101px;padding:25px 18px;display:flex;align-items:center;gap:12px;white-space:nowrap}.brand-mark{width:42px;height:42px;flex:none;object-fit:contain;border-radius:8px;background:#000}.brand-name{font-family:Georgia,serif;font-size:25px;letter-spacing:2px;line-height:1}.brand-caption{font-size:8px;letter-spacing:1.1px;margin-top:7px;color:var(--muted);text-transform:uppercase}.workspace{margin:0 17px 26px;border:1px solid var(--line);border-radius:8px;padding:12px;display:flex;gap:10px;align-items:center;white-space:nowrap}.workspace-icon{display:grid;place-items:center;width:30px;height:30px;background:var(--goldbg);color:var(--gold);border-radius:6px;flex:none}.nav-scroll{flex:1;overflow-y:auto;overflow-x:hidden;padding:0 14px}.nav-label{padding:0 13px;margin-bottom:10px}.nav-item{border:none;background:transparent;border-radius:7px;width:100%;display:flex;justify-content:flex-start;padding:12px 13px;gap:12px;white-space:nowrap;color:var(--muted);margin:3px 0;text-align:left;height:43px}.nav-item:hover{background:var(--panel2);color:var(--text)}.nav-item.active{color:var(--gold);background:var(--goldbg);position:relative}.nav-item.active:before{content:'';height:17px;width:2px;background:var(--gold);position:absolute;left:0;border-radius:2px}.nav-dot{width:9px;height:9px;border-radius:3px;display:inline-block;flex:none;margin:0 4px}.nav-divider{height:1px;background:var(--line);margin:19px 10px}.nav-bottom{padding:12px 14px 18px;border-top:1px solid var(--line)}.local-status{display:flex;gap:8px;align-items:center;font-size:10px;color:var(--muted);padding:13px 13px 5px;white-space:nowrap}.status-dot{height:6px;width:6px;background:var(--green);border-radius:50%;box-shadow:0 0 8px #86bea222;flex:none}.user-block{border-top:1px solid var(--line);padding:18px 22px;gap:10px;white-space:nowrap}.avatar{height:32px;width:32px;border-radius:50%;background:var(--goldbg);color:var(--gold);display:grid;place-items:center;font-family:Georgia,serif;font-size:15px;flex:none}\n#shell{margin-left:244px;transition:margin-left .3s cubic-bezier(.22,.8,.25,1)}header{height:70px;border-bottom:1px solid var(--line);display:flex;align-items:center;justify-content:space-between;padding:0 35px;gap:15px}.breadcrumb{color:var(--muted);font-size:11px;gap:12px}.breadcrumb b{color:var(--text);font-weight:400}.search-btn{background:transparent;color:var(--muted);border:1px solid var(--line);font-size:11px;padding:7px 12px;width:218px;justify-content:flex-start}.search-btn kbd{margin-left:auto;border:1px solid var(--line);font-size:9px;padding:0 4px;border-radius:3px;color:var(--muted)}.top-date{font-size:11px;color:var(--muted)}main{max-width:1640px;margin:auto;padding:32px 35px 26px}.page-head{display:flex;align-items:center;justify-content:space-between;gap:18px;margin:0 0 27px}.page-head p{color:var(--muted);font-size:12px;margin-top:10px}.page-head .eyebrow{margin-bottom:9px}.toolbar{display:flex;gap:9px;align-items:center}.toolbar select{width:auto}.pill{border:1px solid var(--line);background:var(--panel2);border-radius:5px;padding:3px 8px;font-size:10px;display:inline-flex;align-items:center;gap:5px;white-space:nowrap}.pill.green{background:#6eaf8513;border-color:#78b28d25}.pill.red{background:#d87f7012;border-color:#d87f7025}.pill.gold{background:var(--goldbg);border-color:#c7ad7730}.notice{border:1px solid var(--line);border-left:2px solid var(--gold);border-radius:7px;padding:12px 15px;color:var(--muted);font-size:12px;background:var(--panel);margin-bottom:20px}.demo-notice{display:flex;justify-content:space-between;align-items:center;padding:8px 13px;margin-bottom:22px;font-size:11px;background:var(--goldbg);color:var(--gold);border-radius:6px;gap:10px}.demo-notice button{padding:2px 7px;color:var(--gold);font-size:10px;border-color:#c7ad7733;background:transparent}.kpis{display:grid;grid-template-columns:repeat(4,1fr);gap:16px;margin-bottom:23px}.kpi{border:1px solid var(--line);background:var(--panel);border-radius:var(--radius);padding:19px 20px 17px;min-width:0}.kpi-top{display:flex;align-items:center;justify-content:space-between;color:var(--muted);font-size:11px}.kpi-top svg{color:var(--gold);width:16px;height:16px}.kpi-value{font-size:29px;font-family:Georgia,serif;letter-spacing:-.5px;margin-top:13px;font-variant-numeric:tabular-nums;white-space:nowrap}.kpi-bottom{font-size:10px;color:var(--muted);margin-top:10px;display:flex;align-items:center;gap:7px}.panel{border:1px solid var(--line);background:var(--panel);border-radius:var(--radius);overflow:hidden}.panel-head{padding:21px 22px 0;display:flex;justify-content:space-between;gap:12px;align-items:center}.panel-head p{font-size:10px;color:var(--muted);margin-top:5px}.panel-body{padding:22px}.charts-grid{display:grid;grid-template-columns:1.8fr 1fr;gap:20px;margin-bottom:27px}.chart{height:238px;padding:15px 21px 8px}.chart svg{width:100%;height:100%;overflow:visible}.legend{font-size:10px;gap:13px}.legend span{display:flex;align-items:center;gap:5px}.legend i{width:7px;height:7px;border-radius:50%;display:inline-block}.donut-wrap{display:flex;align-items:center;justify-content:center;gap:30px;padding:27px 22px 24px;min-height:236px}.donut{width:164px;height:164px;border-radius:50%;display:grid;place-items:center;position:relative;flex:none}.donut:after{content:'';position:absolute;inset:19px;border-radius:50%;background:var(--panel)}.donut-label{z-index:1;text-align:center}.donut-label b{font-family:Georgia,serif;font-size:27px;font-weight:400}.donut-label small{display:block;color:var(--muted);font-size:10px;margin-top:2px}.donut-legend{display:flex;flex-direction:column;gap:18px;font-size:10px;min-width:95px}.donut-legend .amount{font-size:13px;color:var(--text);padding-left:13px;margin-top:3px}.section-title{display:flex;align-items:center;justify-content:space-between;margin:0 0 15px}.section-title small{color:var(--muted);font-size:11px;font-weight:400;margin-left:9px}.text-link{background:none;border:none;padding:3px 0;color:var(--gold);font-size:11px}.sci-grid{display:grid;grid-template-columns:repeat(3,1fr);gap:17px;margin-bottom:27px}.sci-card{padding:20px;border:1px solid var(--line);background:var(--panel);border-radius:var(--radius);cursor:pointer;transition:border .2s,transform .2s}.sci-card:hover{transform:translateY(-3px);border-color:var(--gold)}.building-icon{width:37px;height:37px;display:grid;place-items:center;border:1px solid var(--line);border-radius:9px;background:var(--panel2);color:var(--gold);flex:none}.sci-card h3{font-size:13px}.sci-card .location{font-size:10px;color:var(--muted);margin-top:4px}.sci-stats{display:grid;grid-template-columns:1fr 1fr;margin-top:21px;gap:15px}.sci-stats label{color:var(--muted);font-size:10px;display:block}.sci-stats strong{font-size:17px;font-family:Georgia,serif;font-weight:400;display:block;margin-top:4px}.sci-card-bottom{border-top:1px solid var(--line);margin-top:18px;padding-top:13px;display:flex;align-items:center;justify-content:space-between;font-size:10px;color:var(--muted)}.mini-bar{display:flex;height:3px;gap:3px;margin-top:14px}.mini-bar i{height:3px;background:var(--green);border-radius:2px;flex:1}.lower-grid{display:grid;grid-template-columns:1.45fr 1fr;gap:20px}.table-wrap{overflow-x:auto}table{width:100%;border-collapse:collapse;white-space:nowrap}th{padding:12px 20px;color:var(--muted);text-align:left;font-size:9px;font-weight:500;letter-spacing:.7px;text-transform:uppercase;border-bottom:1px solid var(--line)}td{padding:14px 20px;border-bottom:1px solid var(--line);font-size:11px}tbody tr:last-child td{border-bottom:0}tbody tr:hover{background:var(--panel2)}td strong{font-size:11px;font-weight:500}.cell-sub{display:block;color:var(--muted);font-size:10px;margin-top:3px}.align-right{text-align:right}.actions{display:flex;justify-content:flex-end;gap:3px}.actions button{padding:4px 6px;min-width:27px;background:transparent;border:0}.actions button svg{width:14px;height:14px}.task-line{padding:15px 21px;display:flex;align-items:center;gap:12px;border-bottom:1px solid var(--line)}.task-line:last-child{border-bottom:0}.task-date{background:var(--panel2);border:1px solid var(--line);border-radius:7px;min-width:39px;text-align:center;padding:4px 6px;font-size:15px;line-height:1.2}.task-date small{font-size:8px;color:var(--muted);display:block;margin-top:3px;text-transform:uppercase}.task-line h3{font-size:11px}.task-line p{font-size:10px;color:var(--muted);margin-top:4px}.task-line .task-right{margin-left:auto}.footer{display:flex;justify-content:space-between;color:var(--muted);font-size:9px;padding:24px 1px 0;gap:12px}.tabs{display:flex;gap:20px;overflow:auto;border-bottom:1px solid var(--line);margin:-2px 0 23px}.tab{background:transparent;border:none;border-radius:0;color:var(--muted);font-size:12px;white-space:nowrap;padding:12px 1px 14px;position:relative}.tab.active{color:var(--gold)}.tab.active:after{content:'';position:absolute;bottom:0;left:0;right:0;height:2px;background:var(--gold)}.tab:hover{background:transparent;color:var(--text)}.filters{display:flex;gap:9px;margin-bottom:17px;align-items:center}.filters input{max-width:310px}.filters select{width:auto;max-width:220px}.empty{padding:48px 22px;text-align:center;color:var(--muted);display:flex;flex-direction:column;align-items:center;justify-content:center}.empty>svg{height:32px;width:32px;color:var(--gold);margin-bottom:12px}.empty h3{color:var(--text);margin-bottom:7px}.empty p{max-width:440px}.empty button{margin-top:18px;padding:10px 18px;border-radius:8px;font-weight:600;box-shadow:0 6px 18px rgba(0,0,0,.18)}.empty button svg{width:16px;height:16px;color:currentColor;margin:0}.settings-grid{display:grid;grid-template-columns:1fr 1fr;gap:20px}.setting-row{display:flex;align-items:center;justify-content:space-between;gap:18px;padding:17px 0;border-bottom:1px solid var(--line)}\n.setting-row>div{flex:1 1 auto;min-width:0}\n.setting-row>.toggle,.setting-row>.theme-choice{flex:0 0 auto}.setting-row:first-child{padding-top:0}.setting-row:last-child{padding-bottom:0;border:0}.setting-row p{font-size:11px;color:var(--muted);margin-top:5px}.theme-choice{display:flex;gap:9px}.theme-choice button.active{border-color:var(--gold);color:var(--gold);background:var(--goldbg)}.order-item{padding:10px 12px;border:1px solid var(--line);border-radius:7px;margin-top:8px;display:flex;align-items:center;gap:9px;background:var(--panel2);font-size:12px}.order-item .actions{margin-left:auto}.order-item.locked{color:var(--muted);background:transparent;border-style:dashed}.toggle{height:23px;width:41px;flex:0 0 auto;border-radius:20px;background:var(--line);padding:3px;position:relative;border:0}.toggle:after{content:'';height:17px;width:17px;position:absolute;left:3px;top:3px;border-radius:50%;background:var(--muted);transition:left .2s}.toggle.on{background:var(--gold)}.toggle.on:after{left:21px;background:#fff}.info-grid{display:grid;grid-template-columns:1fr 1fr;gap:22px}.info-item label{color:var(--muted);font-size:11px;display:block;margin-bottom:5px}.info-item span{font-size:13px}.audit-list{max-height:310px;overflow:auto}.audit-line{padding:12px 0;border-bottom:1px solid var(--line);font-size:11px;display:flex;gap:16px}.audit-line time{color:var(--muted);min-width:115px}.color-dot{width:8px;height:8px;display:inline-block;border-radius:50%;margin-right:6px}.property-grid{display:grid;grid-template-columns:repeat(3,1fr);gap:18px}.property-card{padding:21px}.property-cover{height:100px;border-radius:8px;margin-bottom:17px;background:linear-gradient(130deg,var(--goldbg),var(--panel2));position:relative;overflow:hidden;display:flex;align-items:center;justify-content:center;color:var(--gold)}.property-cover svg{height:65px;width:65px;opacity:.65}.property-cover.has-photo{height:auto;aspect-ratio:16/5}.property-cover img.property-cover-img{position:absolute;inset:0;width:100%;height:100%;object-fit:cover;display:block;z-index:0}.property-cover .pill{position:absolute;top:10px;right:10px;background:var(--panel);z-index:2}.property-metrics{display:flex;justify-content:space-between;margin-top:18px;border-top:1px solid var(--line);padding-top:15px}.property-metrics small{display:block;color:var(--muted);font-size:10px;margin-bottom:4px}.property-metrics strong{font-size:17px;font-family:Georgia,serif;font-weight:400}.compact-note{color:var(--muted);font-size:11px;margin-top:15px}.balance-card{padding:24px;background:linear-gradient(120deg,var(--goldbg),var(--panel));border:1px solid #c7ad7735;border-radius:12px;margin-bottom:20px}.balance-card strong{font-size:33px;font-family:Georgia,serif;font-weight:400}.annual-bars{display:flex;align-items:end;gap:6px;height:90px}.progress{height:5px;background:var(--line);border-radius:5px;overflow:hidden}.progress i{height:100%;display:block;background:var(--gold);border-radius:5px}.search-results{display:flex;flex-direction:column;gap:7px;max-height:420px;overflow:auto}.search-result{padding:13px;text-align:left;justify-content:flex-start}.search-result small{display:block;color:var(--muted)}.modal-backdrop{position:fixed;inset:0;background:#060906b8;backdrop-filter:blur(6px);display:flex;align-items:center;justify-content:center;z-index:80;padding:22px;animation:fade .15s ease}.modal{background:var(--panel);border:1px solid var(--line);border-radius:15px;width:600px;max-width:100%;max-height:91vh;display:flex;flex-direction:column;box-shadow:var(--shadow);animation:modalIn .22s cubic-bezier(.22,1,.36,1)}@keyframes modalIn{from{opacity:0;transform:translateY(10px) scale(.985)}to{opacity:1;transform:none}}.modal.wide{width:780px}.modal.doc-preview-modal{width:980px}.modal-head{display:flex;align-items:center;justify-content:space-between;padding:21px 25px;border-bottom:1px solid var(--line)}.modal-head h2{font-family:Georgia,serif;font-size:23px;font-weight:400}.modal-content{padding:23px 25px;overflow:auto}.modal-footer{display:flex;justify-content:flex-end;gap:9px;padding:17px 25px;border-top:1px solid var(--line)}.form-grid{display:grid;grid-template-columns:1fr 1fr;gap:17px}.field{display:flex;flex-direction:column;gap:7px}.field.full{grid-column:1/-1}.field label{font-size:11px;color:var(--muted)}input,select,textarea{background:var(--bg);color:var(--text);border:1px solid var(--line);border-radius:6px;padding:10px 11px;width:100%;min-width:0}textarea{resize:vertical;min-height:75px}input[type=color]{height:40px;padding:5px}input[type=checkbox]{width:15px;height:15px;accent-color:var(--gold);flex:none;cursor:pointer}input:focus,select:focus,textarea:focus{border-color:var(--gold);outline:1px solid #c7ad7733}.checks{display:grid;grid-template-columns:1fr 1fr;gap:9px;margin:10px 0 20px}.check{display:flex;align-items:center;gap:9px;font-size:12px;border:1px solid var(--line);border-radius:7px;padding:10px;cursor:pointer}.file-drop{border:1px dashed var(--gold);border-radius:8px;padding:19px;margin:12px 0;background:var(--goldbg);color:var(--gold)}.file-drop input{margin-top:12px}.error{padding:10px 12px;border-radius:6px;color:var(--red);background:#df8e8311;font-size:12px;margin-top:15px;white-space:pre-wrap}.toast-container{position:fixed;right:25px;bottom:23px;display:flex;flex-direction:column;gap:8px;z-index:110}.toast{padding:13px 18px;background:var(--panel2);border:1px solid var(--line);border-left:3px solid var(--green);border-radius:8px;box-shadow:var(--shadow);max-width:420px;font-size:12px;animation:slide .2s ease}.toast.error-toast{border-left-color:var(--red)}.loading{padding:120px 20px;text-align:center;color:var(--muted)}.user-lock{margin-left:auto;display:inline-flex;color:var(--muted)}body.collapsed #sidebar{width:76px}body.collapsed #shell{margin-left:76px}body.collapsed .brand{padding:25px 17px}body.collapsed .brand-text,body.collapsed .nav-text,body.collapsed .workspace,body.collapsed .nav-label,body.collapsed .user-details,body.collapsed .user-lock,body.collapsed .user-block svg,body.collapsed .local-status{display:none}body.collapsed .nav-scroll{padding:0 10px}body.collapsed .nav-bottom{padding:12px 10px}body.collapsed .nav-item{padding:12px 17px}body.collapsed .user-block{padding:18px 0;justify-content:center}body.collapsed .nav-divider{margin:18px 8px}body.collapsed .nav-item svg{flex:none}#modal:empty{display:none}.amount{font-variant-numeric:tabular-nums}.mobile-title{display:none}@keyframes fade{from{opacity:0}to{opacity:1}}@keyframes slide{from{opacity:0;transform:translateY(8px)}to{opacity:1;transform:translateY(0)}}@media(min-width:1550px){main{padding:40px 45px}.kpi-value{font-size:34px}.chart{height:260px}.donut-wrap{min-height:258px}.donut{width:180px;height:180px}}\n@media(max-width:1180px){#sidebar{width:218px}#shell{margin-left:218px}main{padding:26px 24px}header{padding:0 24px}.kpi{padding:16px}.kpi-value{font-size:25px}.donut-wrap{gap:17px;padding:28px 15px}.donut{width:140px;height:140px}.sci-grid{gap:12px}.sci-card{padding:16px}.top-date{display:none}.charts-grid{grid-template-columns:1.5fr 1fr}.property-grid{grid-template-columns:repeat(2,1fr)}}\n@media(max-width:950px){.kpis{grid-template-columns:repeat(2,1fr)}.charts-grid,.lower-grid,.settings-grid{grid-template-columns:1fr}.sci-grid{grid-template-columns:1fr}.donut-wrap{min-height:225px}.sci-stats{grid-template-columns:1fr 1fr}.chart{height:250px}.page-head{align-items:flex-start}.toolbar{flex-wrap:wrap;justify-content:flex-end}.search-btn{width:150px}.search-btn kbd{display:none}.sci-card-bottom{margin-top:14px}}\n@media(max-width:640px){#sidebar{width:76px}#shell{margin-left:76px}.brand{padding:25px 17px}.brand-text,.nav-text,.workspace,.nav-label,.user-details,.user-lock,.user-block svg,.local-status{display:none}.nav-scroll{padding:0 10px}.nav-bottom{padding:12px 10px}.nav-item{padding:12px 17px}.user-block{padding:18px 0;justify-content:center}.nav-divider{margin:18px 8px}header{padding:0 15px;height:60px}.breadcrumb{display:none}.search-btn{width:145px}main{padding:22px 14px}.page-head{flex-direction:column;gap:16px}h1{font-size:29px}.toolbar{justify-content:flex-start}.kpis{gap:10px}.kpi{padding:13px}.kpi-value{font-size:24px}.kpi-top{font-size:10px}.kpi-bottom{font-size:9px}.property-grid{grid-template-columns:1fr}.form-grid,.info-grid{grid-template-columns:1fr}.checks{grid-template-columns:1fr}.modal-backdrop{padding:10px}.modal-content{padding:18px}.modal-head{padding:17px}.footer{flex-direction:column}.legend{gap:7px;font-size:9px}.filters{flex-wrap:wrap}.panel-head{padding:18px 16px 0}.panel-body{padding:17px}.chart{padding:15px 10px}.demo-notice{align-items:flex-start} .setting-row{flex-wrap:wrap}.tabs{gap:17px}}\n.update-steps{padding-left:22px;margin:20px 0;line-height:2.2}.tabs button{white-space:nowrap}.tabs{overflow-x:auto}\n/* Tri des tableaux : seul l'en-tête est cliquable, jamais une cellule. */\nth.sortable{cursor:pointer;user-select:none;-webkit-user-select:none;position:relative;white-space:nowrap;transition:color .15s}\nth.sortable:hover,th.sortable:focus-visible{color:var(--gold)}\nth.sortable:focus-visible{outline:1px solid var(--gold);outline-offset:2px;border-radius:4px}\nth.sortable .sort-mark{display:inline-flex;align-items:center;margin-left:6px;vertical-align:-2px;opacity:.35;transition:opacity .15s}\nth.sortable:hover .sort-mark{opacity:.7}\nth.sortable[data-sort-dir=asc] .sort-mark,th.sortable[data-sort-dir=desc] .sort-mark{opacity:1;color:var(--gold)}\nth.sortable[data-sort-dir=asc],th.sortable[data-sort-dir=desc]{color:var(--gold)}\n.sort-icon{width:11px;height:11px;fill:none;stroke:currentColor;stroke-width:1.5;stroke-linecap:round;stroke-linejoin:round;display:block}\ntable.table-sorted:not(.table-date-sorted) tr.month-total-row{display:none}\n@media print{th.sortable .sort-mark{display:none}}\n@media(prefers-reduced-motion:reduce){th.sortable,th.sortable .sort-mark{transition:none}}\n"

DOMINIS_SORT_JS = 'const TABLE_SORTS=new Map();\nconst SORT_COLLATOR=new Intl.Collator(\'fr\',{numeric:true,sensitivity:\'base\'});\nlet sortBusy=false,sortTimer=null,sortObserver=null,sortNotified=false;\n\nfunction sortIconMark(dir){\n    if(dir===\'asc\')return \'<svg class="sort-icon" viewBox="0 0 12 12" aria-hidden="true"><path d="M6 9.6V2.6M3.1 5.5 6 2.6l2.9 2.9"/></svg>\';\n    if(dir===\'desc\')return \'<svg class="sort-icon" viewBox="0 0 12 12" aria-hidden="true"><path d="M6 2.4v7M3.1 6.5 6 9.4l2.9-2.9"/></svg>\';\n    return \'<svg class="sort-icon sort-icon-idle" viewBox="0 0 12 12" aria-hidden="true"><path d="M4 4.6 6 2.6l2 2M4 7.4l2 2 2-2"/></svg>\';\n}\nfunction sortKeyOfTable(table){\n    if(table.dataset.sortKey)return table.dataset.sortKey;\n    let path=[],el=table;\n    while(el&&el.parentElement&&el.id!==\'main\'&&el.id!==\'modal\'){\n        path.unshift(Array.prototype.indexOf.call(el.parentElement.children,el));\n        el=el.parentElement;\n    }\n    return (page||\'\')+\'/\'+(table.closest(\'#modal\')?\'modal\':\'page\')+\'/\'+path.join(\'.\');\n}\nfunction sortCellText(cell){\n    let clone=cell.cloneNode(true);\n    clone.querySelectorAll(\'.cell-sub,button,input,select,textarea,svg,[data-sort-ignore]\').forEach(n=>n.remove());\n    return (clone.textContent||\'\').replace(/[\\u00a0\\u202f\\u2009]/g,\' \').replace(/\\s+/g,\' \').trim();\n}\nfunction sortCellValue(cell){\n    let text=sortCellText(cell);\n    if(!text||text===\'—\'||text===\'–\'||text===\'-\')return {empty:true};\n    let num=text.replace(/[\\s\\u00a0\\u202f\\u2009]/g,\'\').replace(/€/g,\'\').replace(/\\+/g,\'\').replace(/−/g,\'-\');\n    if(/^\\(.*\\)$/.test(num))num=\'-\'+num.slice(1,-1);\n    if(/^-?\\d+(?:[.,]\\d+)?%?$/.test(num)){\n        let v=parseFloat(num.replace(\'%\',\'\').replace(\',\',\'.\'));\n        if(isFinite(v))return {num:v};\n    }\n    let fr=text.match(/^(\\d{1,2})[\\/.](\\d{1,2})[\\/.](\\d{4})\\b/);   // « 05/03/2025 → 31/12/2027 »\n    if(fr)return {num:Number(fr[3])*10000+Number(fr[2])*100+Number(fr[1])};\n    let iso=text.match(/^(\\d{4})-(\\d{2})-(\\d{2})/);\n    if(iso)return {num:Number(iso[1])*10000+Number(iso[2])*100+Number(iso[3])};\n    return {text:text};\n}\nfunction sortCompare(a,b){\n    if(a.empty||b.empty){\n        if(a.empty&&b.empty)return 0;\n        return a.empty?1:-1;                     // les cellules vides restent en bas\n    }\n    if(\'num\' in a&&\'num\' in b)return a.num-b.num;\n    if(\'num\' in a)return -1;\n    if(\'num\' in b)return 1;\n    if(\'text\' in a&&\'text\' in b)return SORT_COLLATOR.compare(a.text,b.text);\n    return 0;\n}\nfunction sortBodyRows(table){\n    let body=table.tBodies[0];\n    return body?Array.prototype.slice.call(body.rows):[];\n}\nfunction prepareSortTable(table){\n    if(!table||table.dataset.noSort===\'1\'||table.dataset.sortReady===\'1\')return false;\n    if(table.closest(\'.doc-preview-sheet,.doc-preview-stage,.doc-preview-viewport\'))return false;\n\n    let head=table.tHead,body=table.tBodies[0];\n    if(!head||!body||!head.rows.length)return false;\n    let headRow=head.rows[head.rows.length-1];\n    let ths=Array.prototype.slice.call(headRow.cells);\n    if(!ths.length||ths.some(th=>th.colSpan>1||th.rowSpan>1))return false;\n    let rows=sortBodyRows(table);\n    let movable=rows.filter(r=>!r.classList.contains(\'month-total-row\')&&!r.classList.contains(\'sort-fixed\')&&!r.querySelector(\'td[colspan]\'));\n    if(movable.length<2)return false;\n    if(movable.some(r=>r.cells.length<ths.length))return false;\n    rows.forEach((r,i)=>{r.dataset.sortPos=String(i);});\n    // Une colonne dont toutes les cellules sont vides n\'a rien à trier :\n    // afficher une flèche sans effet serait trompeur.\n    let emptyCols=ths.map((th,index)=>movable.every(r=>!r.cells[index]||sortCellValue(r.cells[index]).empty));\n    table.dataset.sortReady=\'1\';\n    ths.forEach((th,index)=>{\n        if(th.querySelector(\'button,a,input,select\'))return;\n        if(!sortCellText(th))return;\n        if(emptyCols[index])return;\n        th.classList.add(\'sortable\');\n        th.dataset.sortIndex=String(index);\n        th.tabIndex=0;\n        let mark=document.createElement(\'span\');\n        mark.className=\'sort-mark\';\n        mark.innerHTML=sortIconMark(\'none\');\n        th.appendChild(mark);\n        paintSortHeader(th,\'none\');\n    });\n    return true;\n}\nfunction paintSortHeader(th,dir){\n    dir=dir||\'none\';\n    // Rien à changer : ne pas toucher au DOM, sinon l\'observateur de mutations\n    // relancerait un tri à chaque passage (boucle infinie).\n    if(th.dataset.sortDir===dir)return;\n    th.dataset.sortDir=dir;\n    th.setAttribute(\'aria-sort\',dir===\'asc\'?\'ascending\':dir===\'desc\'?\'descending\':\'none\');\n    let mark=th.querySelector(\'.sort-mark\');\n    if(mark)mark.innerHTML=sortIconMark(dir);\n    let name=sortCellText(th)||\'cette colonne\';\n    th.title=dir===\'asc\'?(\'Trié croissant sur « \'+name+\' » — cliquer pour trier décroissant\')\n        :dir===\'desc\'?(\'Trié décroissant sur « \'+name+\' » — cliquer pour revenir à l’ordre d’origine\')\n        :(\'Trier par « \'+name+\' »\');\n}\nfunction sortPaintTable(table,state){\n    let head=table.tHead;\n    if(!head||!head.rows.length)return;\n    Array.prototype.slice.call(head.rows[head.rows.length-1].cells).forEach((th,index)=>{\n        if(!th.classList.contains(\'sortable\'))return;\n        let dir=(state&&Number(state.index)===index)?state.dir:\'none\';\n        paintSortHeader(th,dir);\n    });\n}\nfunction sortSameOrder(body,ordered){\n    let current=Array.prototype.slice.call(body.rows);\n    if(current.length!==ordered.length)return false;\n    for(let i=0;i<current.length;i++)if(current[i]!==ordered[i])return false;\n    return true;\n}\nfunction sortPlace(body,ordered){\n    if(sortSameOrder(body,ordered))return false;   // aucun déplacement inutile\n    ordered.forEach(r=>body.appendChild(r));\n    return true;\n}\nfunction sortRestoreOrder(table){\n    let body=table.tBodies[0];\n    if(!body)return;\n    let rows=Array.prototype.slice.call(body.rows);\n    let ordered=rows.slice().sort((a,b)=>(Number(a.dataset.sortPos||0))-(Number(b.dataset.sortPos||0)));\n    sortPlace(body,ordered);\n    table.classList.remove(\'table-sorted\',\'table-date-sorted\');\n}\nfunction sortApply(table,index,dir){\n    let body=table.tBodies[0];\n    if(!body)return;\n    let rows=Array.prototype.slice.call(body.rows);\n    rows.forEach((r,i)=>{if(r.dataset.sortPos===undefined)r.dataset.sortPos=String(i);});\n    let isSticky=r=>r.classList.contains(\'month-total-row\');\n    let isFixed=r=>r.classList.contains(\'sort-fixed\')||!!r.querySelector(\'td[colspan]\');\n    let movable=rows.filter(r=>!isSticky(r)&&!isFixed(r));\n    let sticky=rows.filter(isSticky);\n    let fixed=rows.filter(r=>!isSticky(r)&&isFixed(r));\n    movable.sort((a,b)=>{\n        let va=sortCellValue(a.cells[index]),vb=sortCellValue(b.cells[index]);\n        // Une cellule vide reste en bas dans les deux sens de tri.\n        if(va.empty||vb.empty){\n            if(va.empty&&vb.empty)return Number(a.dataset.sortPos||0)-Number(b.dataset.sortPos||0);\n            return va.empty?1:-1;\n        }\n        let c=sortCompare(va,vb);\n        if(c)return dir===\'desc\'?-c:c;\n        return Number(a.dataset.sortPos||0)-Number(b.dataset.sortPos||0);   // tri stable\n    });\n    let chronological=table.tHead.rows[table.tHead.rows.length-1].cells[index].dataset.sortColumn===\'date\';\n    let ordered=[];\n    if(chronological){\n        let totals=new Map(sticky.map(r=>[r.dataset.month,r])),used=new Set();\n        movable.forEach((r,i)=>{\n            let month=r.dataset.month,total=totals.get(month);\n            // En décroissant, le cumul précède le mois ; en croissant, il le clôt.\n            if(dir===\'desc\'&&total&&!used.has(month)){ordered.push(total);used.add(month);}\n            ordered.push(r);\n            if(dir===\'asc\'&&total&&(!movable[i+1]||movable[i+1].dataset.month!==month)){\n                ordered.push(total);used.add(month);\n            }\n        });\n        ordered.push(...fixed,...sticky.filter(r=>!used.has(r.dataset.month)));\n    }else ordered=movable.concat(fixed,sticky);\n    sortPlace(body,ordered);\n    table.classList.add(\'table-sorted\');\n    table.classList.toggle(\'table-date-sorted\',chronological);\n}\nfunction sortResolveIndex(table,state){\n    let head=table.tHead;\n    if(!head||!head.rows.length)return null;\n    let ths=Array.prototype.slice.call(head.rows[head.rows.length-1].cells);\n    let label=(state.label||\'\').trim();\n    if(label){\n        let found=-1;\n        ths.forEach((th,index)=>{if(found<0&&th.classList.contains(\'sortable\')&&sortCellText(th)===label)found=index;});\n        if(found>=0)return found;\n        return null;                    // colonne masquée ou renommée : plus de tri\n    }\n    let th=ths[Number(state.index)];\n    return th&&th.classList.contains(\'sortable\')?Number(state.index):null;\n}\nfunction sortApplyState(table,state){\n    if(!state||state.dir===\'none\'||state.index==null){sortRestoreOrder(table);sortPaintTable(table,null);return;}\n    let index=sortResolveIndex(table,state);\n    if(index===null){sortRestoreOrder(table);sortPaintTable(table,null);return;}\n    sortApply(table,index,state.dir);\n    sortPaintTable(table,{index:index,dir:state.dir,label:state.label});\n}\nfunction tableSortInit(root){\n    if(sortBusy)return;\n    sortBusy=true;\n    try{\n        let tables=Array.prototype.slice.call((root||document).querySelectorAll(\'#main table, #modal table, #listing table\'));\n        tables.forEach(prepareSortTable);\n        \n        tables.forEach(table=>{\n            if(table.dataset.sortReady!==\'1\')return;\n            let state=TABLE_SORTS.get(sortKeyOfTable(table));\n            if(state)sortApplyState(table,state);\n        });\n    }finally{sortBusy=false;}\n}\nfunction tableSortCycle(th){\n    let table=th&&th.closest?th.closest(\'table\'):null;\n    if(!table||table.dataset.sortReady!==\'1\')return;\n    let key=sortKeyOfTable(table),index=Number(th.dataset.sortIndex);\n    let current=TABLE_SORTS.get(key)||{index:null,dir:\'none\'};\n    let next;\n    let label=sortCellText(th)||\'\';\n    // Le titre suit l\'état : si une colonne est masquée par les réglages du\n    // tableau, le tri ne se décale pas sur sa voisine.\n    if(sortResolveIndex(table,current)!==index||current.dir===\'none\')next={index:index,dir:\'asc\',label:label};\n    else if(current.dir===\'asc\')next={index:index,dir:\'desc\',label:label};\n    else next={index:null,dir:\'none\'};\n    if(next.dir===\'none\')TABLE_SORTS.delete(key);else TABLE_SORTS.set(key,next);\n    sortBusy=true;\n    try{sortApplyState(table,next);}finally{sortBusy=false;}\n    let name=(sortCellText(th)||\'colonne\').toLowerCase();\n    let hidden=!table.classList.contains(\'table-date-sorted\')&&table.querySelectorAll(\'tr.month-total-row\').length;\n    notify(next.dir===\'none\'?\'Tri désactivé : ordre d’origine rétabli.\'\n        :\'Tri \'+(next.dir===\'asc\'?\'croissant\':\'décroissant\')+\' sur « \'+name+\' ».\'\n         +(hidden?\' Les cumuls mensuels sont masqués pendant le tri.\':\'\'));\n}\n'

HTML = HTML.replace('__CSS__', DOMINIS_CSS).replace('__SORT_JS__', DOMINIS_SORT_JS)

if __name__ == '__main__':
    try:
        import multiprocessing
        multiprocessing.freeze_support()
        sys.exit(main())
    except KeyboardInterrupt:
        STOP.set()
    except Exception as exc:
        logging.exception('Démarrage impossible')
        message = 'MMA Comptabilité ne peut pas démarrer.\n\n' + str(exc)
        if isinstance(exc, ImportError):
            message += '\n\nInstallez les dépendances : python -m pip install -r requirements.txt'
        if os.name == 'nt':
            import ctypes
            ctypes.windll.user32.MessageBoxW(None, message, APP_NAME, 0x10)
        else:
            print(message, file=sys.stderr)
        sys.exit(1)
