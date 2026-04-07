@echo off
setlocal

set "SCRIPT_DIR=%~dp0"
set "SOURCE_WAD=%SCRIPT_DIR%rogue_doom.wad"
set "DEST_DIR=C:\Portable\GZDoom\X"
set "DEST_WAD=%DEST_DIR%\rogue_doom.wad"
set "GZDOOM_DIR=C:\Portable\GZDoom"
set "GZDOOM_EXE=%GZDOOM_DIR%\gzdoom.exe"
set "SAVE_DIR=X\save_rogue_doom_diag"
set "MOD1=X\VoxelDoom_v2.4_bdbarrel_compat.pk3"
set "MOD2=X\CatsVisorBASE1.10.3.pk3"
set "MOD3=X\brutal21_weapons_only_Zandronum_fix_barrel_noswivel.pk3"
set "MOD4=X\LTP_V6.8.pk3"
set "MOD5=X\gearbox-v0.7.2.pk3"

pushd "%SCRIPT_DIR%" || exit /b 1

c:\Portable\WinPython\python\python.exe rogue_doom.py --seed 20260404
if errorlevel 1 (
    echo ERROR: rogue_doom.py failed.
    popd
    exit /b 1
)



if not exist "%SOURCE_WAD%" (
    echo ERROR: Generated WAD not found: "%SOURCE_WAD%"
    popd
    exit /b 1
)

if not exist "%DEST_DIR%" (
    mkdir "%DEST_DIR%"
)

copy /Y "%SOURCE_WAD%" "%DEST_WAD%" >nul
if errorlevel 1 (
    echo ERROR: Failed to copy WAD to "%DEST_WAD%"
    popd
    exit /b 1
)
if not exist "%GZDOOM_EXE%" (
    echo ERROR: GZDoom executable not found: "%GZDOOM_EXE%"
    popd
    exit /b 1
)
cd /d "%GZDOOM_DIR%"
start "" "%GZDOOM_EXE%" -iwad doom2 -file ^
    "%MOD1%" ^
    "%MOD2%" ^
    "%MOD3%" ^
    "%MOD4%" ^
    "%MOD5%" ^
    "X\rogue_doom.wad" ^
    -savedir "%SAVE_DIR%" ^
    +logfile "C:\Portable\WinPython\WORK\doom\gzdoom_lastrun.log"
popd
endlocal
timeout /t 20 >nul
