#!/bin/sh

if test "x$OS" = "xWindowsNT"; then
   os=win32
   ws=win32
   arch=x86
else
   os=linux
   ws=gtk
   if test `uname -m` = "x86_64"; then
     arch=x86_64
   else
     arch=x86
   fi
fi

$ECLIPSE_HOME/eclipse \
    -nosplash -application org.eclipse.ant.core.antRunner \
    --launcher.suppressErrors \
    -buildfile build.xml      \
    -Dos=${os} -Dws=${ws} -Darch=${arch} release


