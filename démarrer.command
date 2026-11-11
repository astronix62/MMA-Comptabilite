#!/bin/bash
# Lanceur macOS : ne recherche ni ne lance Dominis.
set -eu
MMA_ROOT="$(cd -- "$(dirname -- "$0")" && pwd -P)"
cd "$MMA_ROOT"
MMA_DATA_DIR="$HOME/Library/Application Support/MMA Comptabilite"

fail() {
    printf '\n%s\n' "$1" >&2
    printf 'Appuyez sur Entrée pour fermer ce terminal.\n' >&2
    read -r _mma_answer || true
    exit 1
}
trap 'fail "Le lancement de MMA Comptabilité a échoué. Consultez le message ci-dessus."' ERR

if [ "$(uname -s)" != Darwin ]; then
    fail "Ce lanceur est destiné à macOS. Sous Windows, utilisez démarrer.bat."
fi

if [ -d "$MMA_ROOT/dist/MMA Comptabilité.app" ]; then
    exec /usr/bin/open "$MMA_ROOT/dist/MMA Comptabilité.app" --args --data-dir "$MMA_DATA_DIR"
fi

MMA_PYTHON="$MMA_ROOT/.venv-macos/bin/python"
if [ ! -x "$MMA_PYTHON" ]; then
    MMA_SYSTEM_PYTHON="$(command -v python3.13 || command -v python3 || true)"
    if [ -z "$MMA_SYSTEM_PYTHON" ]; then
        fail "Installez Python 3.13 pour macOS, ou placez l’application compilée dans dist/MMA Comptabilité.app."
    fi
    "$MMA_SYSTEM_PYTHON" -c 'import sys; assert sys.version_info >= (3,10), "Python 3.10 minimum ; Python 3.13 conseillé."'
    "$MMA_SYSTEM_PYTHON" -m venv "$MMA_ROOT/.venv-macos"
fi

if ! "$MMA_PYTHON" -c 'import webview, openpyxl, pypdf, certifi' >/dev/null 2>&1; then
    printf 'Installation initiale des dépendances dans .venv-macos.\nUne connexion Internet est nécessaire pour cette installation uniquement.\n'
    "$MMA_PYTHON" -m pip install -r "$MMA_ROOT/requirements.txt"
fi

"$MMA_PYTHON" "$MMA_ROOT/MMA_Comptabilite.py" --data-dir "$MMA_DATA_DIR"
