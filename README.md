# MMA Comptabilité

Application de bureau pour **MMA Fight Club Calais**, adaptée de Dominis. Comptabilité de trésorerie locale ; aucun abonnement, serveur distant ou compte utilisateur requis.

## Démarrer simplement

- **Windows :** double-cliquer sur `démarrer.bat`. Le lanceur ouvre en priorité l'exécutable présent dans `dist/`, sans installation de Python.
- **macOS :** double-cliquer sur `démarrer.command`. Le lanceur utilise `dist/MMA Comptabilité.app` si elle existe ; sinon il utilise Python 3.13 installé sur le Mac.

En mode Python, les lanceurs créent un environnement propre au projet (`.venv-windows` ou `.venv-macos`) et installent les dépendances manquantes au premier lancement. Cette installation nécessite Internet ; l'utilisation comptable reste ensuite locale. Si le fichier `.command` copié depuis Windows n'est pas exécutable, ouvrir Terminal dans ce dossier et lancer une fois :

```bash
chmod +x "démarrer.command"
```

Il n'y a pas encore de `.app` compilée livrée dans ce dossier : sur Mac, Python est donc nécessaire tant que le build macOS n'a pas été réalisé. La syntaxe du lanceur est contrôlée ; son exécution sur un Mac reste à vérifier.

## Exécutable Windows

Ouvrir `dist/MMA Comptabilité.exe`. Le programme contient Python et ses bibliothèques et ouvre sa propre fenêtre. Le moteur système **Microsoft WebView2** doit être disponible ; il était présent sur le Windows 11 utilisé pour les tests. L'exécutable n'est pas signé : Windows peut afficher un avertissement SmartScreen.

Une seule copie de l'exécutable est conservée dans `dist/`. Les copies destinées aux Releases seront régénérées par `tools/build.py` au besoin. Ne pas lancer deux instances sur le même dossier de données.

## Lancer le fichier Python

Python 3.13 conseillé (version testée : 3.13.7).

```powershell
python -m pip install -r requirements.txt
python MMA_Comptabilite.py
```

Le mode normal utilise exclusivement une fenêtre pywebview. Il ne se replie pas vers un navigateur externe si une dépendance manque. Le code, le logo, l'interface, les lecteurs et les rapports sont réunis dans `MMA_Comptabilite.py`. `Dominis.py` n'est pas nécessaire à l'exécution et n'a pas été modifié.

## Première utilisation

1. Dans **Comptes**, définir le solde initial de la banque et de la caisse, et sa date, avant de saisir leurs premiers mouvements. Ce solde est celui **avant** les opérations du jour choisi.
2. Vérifier les dates de l'exercice et les catégories.
3. Saisir une recette, une dépense ou un virement interne. Le montant reste positif ; le sens détermine son effet.
4. Joindre les justificatifs. Pointer les mouvements retrouvés sur les relevés et utiliser **Comparer au relevé**.
5. Créer les prévisions budgétaires, consulter les synthèses, puis clôturer l'exercice après vérification.

Les exercices peuvent suivre une saison sportive, avec des dates libres sans chevauchement. Aucune gestion autonome des adhérents, entraînements ou compétitions n'est incluse. Les cotisations sont des recettes.

## Données et sauvegardes

Le fichier se nomme exactement **Data.db**. Il contient les opérations, paramètres, budgets, historique et justificatifs : une sauvegarde SQLite constitue donc une copie complète.

| Système | Emplacement par défaut |
|---|---|
| Windows | `%LOCALAPPDATA%\MMA Comptabilite\Data.db` |
| macOS | `~/Library/Application Support/MMA Comptabilite/Data.db` |

Le chemin exact est affiché dans les paramètres. Le dossier du programme est distinct : déplacer, remplacer ou réinstaller l'exécutable ne réinitialise pas la base. Aucun `Data.db` n'est livré dans les distributions.

**Séparation de Dominis :** les deux lanceurs imposent le dossier utilisateur `MMA Comptabilite` et ne transmettent aucun chemin fourni en argument externe. MMA Comptabilité n'importe pas le programme Dominis, ne recherche pas sa base et ne reprend pas automatiquement ses données. Un identifiant interne SQLite propre à MMA est vérifié à l'ouverture et à la restauration : une base Dominis est refusée sans écrasement. Seul un import JSON Dominis explicitement choisi, vérifié puis confirmé dans l'interface peut reprendre volontairement des mouvements.

Le ménage du dossier a retiré les caches, constructions intermédiaires, bases/captures d'essai, anciennes archives et distributions en double. `Dominis.py`, le programme MMA, ses lanceurs, le logo, l'exécutable, la documentation, les tests et les outils de construction/publication sont conservés.

Sauvegardes dans `sauvegardes/` : au démarrage, toutes les 15 minutes, à la fermeture et avant import, suppression, clôture/réouverture, restauration, migration ou mise à jour. Les 48 dernières copies automatiques sont conservées. Les copies manuelles, de fermeture et de précaution ne sont pas purgées automatiquement ; surveiller leur espace disque. Chaque copie utilise l'API SQLite Backup et passe les contrôles d'intégrité avant publication.

**Copier sur un autre support** permet de choisir un disque externe. Les copies sur le disque d'origine ne protègent pas d'une panne matérielle de ce disque. Les données ne sont pas chiffrées ; leur confidentialité dépend du compte système et du chiffrement du disque.

Une restauration demande de saisir `RESTAURER` et conserve une copie préalable. Si la base ne s'ouvre plus, un écran de récupération permet de choisir une sauvegarde et conserve le fichier original dans `recuperation/`. Si `Data.db` a disparu alors que des sauvegardes existent, un avertissement persistant bloque les nouvelles saisies et la rotation des copies automatiques jusqu’à la restauration.

## Imports et exports

- **CSV / TSV** : détection du séparateur, correspondance des colonnes, dates françaises/ISO, montant signé ou colonnes débit/crédit.
- **XLSX** : choix de feuille et ligne d'en-tête ; option lecteur avancé Dominis pour tableaux multiples, formules simples et contrôles de soldes. Les soldes initiaux proposés ne sont jamais appliqués automatiquement.
- **JSON MMA / Dominis / Auréa** : reprise des mouvements uniquement, avec choix du compte et vérification des catégories. Le JSON n'est pas une sauvegarde complète.
- **PDF / TXT** : propositions textuelles de relevé à vérifier/corriger. Pas d'OCR : les scans nécessitent une saisie manuelle.
- **Exports** : XLSX, CSV protégé contre les formules injectées, JSON, rapport PDF et historique JSON intégral. Ils reprennent l'exercice et le compte sélectionnés ; les filtres de texte et de sens du journal ne limitent pas les exports.

L'aperçu permet de modifier les lignes et de les sélectionner. La confirmation effectue une transaction unique : une ligne invalide bloque tout le lot. Les doublons exacts (date, libellé normalisé, montant, sens et comptes) sont ignorés. Pour deux paiements réellement distincts mais identiques sur ces champs, les enregistrer manuellement avec une référence/libellé distinctif. Import limité à 10 000 lignes et 30 Mo par fichier.

Les justificatifs acceptent tout format ; aperçu interne pour PDF, images courantes, texte/CSV/JSON, XLSX et DOCX. Les autres formats s'exportent pour consultation. Les originaux sont conservés sans retouche destructive.

## Construction et Releases

Voir [docs/DISTRIBUTION.md](docs/DISTRIBUTION.md) pour les commandes, les noms d'assets, la publication et les signatures. La configuration GitHub Actions produit Windows x64, macOS Intel et macOS Apple Silicon. La compilation macOS doit s'effectuer sur macOS ; elle n'a pas été exécutée sur ce poste Windows.

## Validation et limites

Voir [docs/VALIDATION.md](docs/VALIDATION.md) et [docs/ANALYSE.md](docs/ANALYSE.md) pour les tests et les choix de reprise de Dominis.

Les transitions et le style du club sont décrits dans [docs/INTERFACE.md](docs/INTERFACE.md). Les animations se désactivent dans les paramètres et respectent les préférences de mouvement réduit du système.

Il s'agit d'une comptabilité de trésorerie en euros. Le programme ne revendique pas une conformité réglementaire, ne tient pas de comptabilité en partie double et ne produit pas de bilan statutaire, FEC, déclaration fiscale ni reçu fiscal. Les besoins propres du club doivent être confirmés avec son comptable si ces documents sont requis.
