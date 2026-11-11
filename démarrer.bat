@echo off
chcp 65001 >nul
setlocal DisableDelayedExpansion
cd /d "%~dp0"
title MMA Comptabilité
rem Dossier exclusivement reserve a MMA Comptabilite, jamais celui de Dominis.
set "MMA_DATA_DIR=%LOCALAPPDATA%\MMA Comptabilite"
if not defined LOCALAPPDATA set "MMA_DATA_DIR=%USERPROFILE%\AppData\Local\MMA Comptabilite"
if not exist "%~dp0dist\MMA Comptabilité.exe" goto python_mode
start "" "%~dp0dist\MMA Comptabilité.exe" --data-dir "%MMA_DATA_DIR%"
exit /b 0

:python_mode
set "MMA_PYTHON=%~dp0.venv-windows\Scripts\python.exe"
if exist "%MMA_PYTHON%" goto dependencies
echo Preparation du lancement Python de MMA Comptabilite...
py -3.13 -c "import sys; assert sys.version_info >= (3,10)" >nul 2>&1
if not errorlevel 1 goto create_py313
py -3 -c "import sys; assert sys.version_info >= (3,10)" >nul 2>&1
if not errorlevel 1 goto create_py
python -c "import sys; assert sys.version_info >= (3,10)" >nul 2>&1
if errorlevel 1 goto no_python
python -m venv "%~dp0.venv-windows"
goto check_venv
:create_py313
py -3.13 -m venv "%~dp0.venv-windows"
goto check_venv
:create_py
py -3 -m venv "%~dp0.venv-windows"
:check_venv
if errorlevel 1 goto failed
if not exist "%MMA_PYTHON%" goto failed
:dependencies
"%MMA_PYTHON%" -c "import webview, openpyxl, pypdf, certifi" >nul 2>&1
if not errorlevel 1 goto launch
echo Installation initiale des dependances dans .venv-windows.
echo Une connexion Internet est necessaire pour cette installation uniquement.
"%MMA_PYTHON%" -m pip install -r "%~dp0requirements.txt"
if errorlevel 1 goto failed
:launch
"%MMA_PYTHON%" "%~dp0MMA_Comptabilite.py" --data-dir "%MMA_DATA_DIR%"
if errorlevel 1 goto failed
exit /b 0
:no_python
echo Python est introuvable. Installez Python 3.13 ou utilisez l'executable Windows.
pause
exit /b 1
:failed
echo Le lancement a echoue. Consultez le message ci-dessus et le guide README.md.
echo Aucune base Dominis n'est selectionnee par ce lanceur.
pause
exit /b 1
