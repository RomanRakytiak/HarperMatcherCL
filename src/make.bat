if %PROCESSOR_ARCHITECTURE% equ x86 (set CLPATH=C:\Program Files\CL) else set CLPATH=C:\Program Files (x86)\CL
"%CLPATH%\runcl.exe" -c mtex.cl
"%CLPATH%\runcl.exe" -c maux.cl
"%CLPATH%\runcl.exe" -c msyntax.cl
"%CLPATH%\runcl.exe" -c mdebug.cl
"%CLPATH%\runcl.exe" -c msemantics.cl
"%CLPATH%\runcl.exe" -c mnorm.cl
"%CLPATH%\runcl.exe" -c mmatcher.cl
