
rem @echo off 
    setlocal enableextensions disabledelayedexpansion

    rem Where to find java information in registry
    set "javaKey=HKLM\SOFTWARE\JavaSoft\Java Runtime Environment"

    rem Get current java version
    set "javaVersion="
    for /f "tokens=3" %%v in ('reg query "%javaKey%" /v "CurrentVersion" 2^>nul') do set "javaVersion=%%v"

    rem Test if a java version has been found
    if not defined javaVersion (
        echo Java version not found
        goto endProcess
    )

    rem Get java home for current java version
    set "javaDir="
    for /f "tokens=2,*" %%d in ('reg query "%javaKey%\%javaVersion%" /v "JavaHome" 2^>nul') do set "javaDir=%%e"

    if not defined javaDir (
        echo Java directory not found
    ) else (
        echo JAVA_HOME : %javaDir%
    )

:endProcess 
    endlocal

SET mypath=%~dp0
echo %mypath:~0,-1%

rem <call> %*

if defined ProgramFiles(x86) (
    @echo yes
    @echo Some 64-bit work
) else (
    @echo no
    @echo Some 32-bit work
)

%javaDir%/bin/java -classpath %mypath%/lib/svutils.jar net.sf.sveditor.svutils %*

