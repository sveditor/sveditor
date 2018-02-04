#!/bin/sh

is_mingw=`uname | sed -e 's/MINGW.*$/1/'`

if test "$is_mingw" = "1"; then
  os=win32
  ws=win32
  arch=x86_64
  eclipse=eclipsec
else
  os=linux
  ws=gtk
  if test `uname -m` = "x86_64"; then
    arch=x86_64
  else
    arch=x86
  fi
  eclipse=eclipse
fi

$ECLIPSE_HOME/${eclipse} \
    -nosplash -application org.eclipse.ant.core.antRunner \
    --launcher.suppressErrors \
    -buildfile mk_sve.xml mk_sve

#    -Dos=${os} -Dws=${ws} -Darch=${arch} mk_sve

#    -Dos=${os} -Darch=${arch} -Dc_os=${os} -Dc_arch=${arch} -Dc_ws=${ws} build_archive

