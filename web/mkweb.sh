#!/bin/sh

is_mingw=`uname | sed -e 's/MINGW.*$/1/'`

if test "$is_mingw" = "1"; then
  os=win32
  ws=win32
  eclipse=eclipsec
else
  os=linux
  ws=gtk
  eclipse=eclipse
fi

$ECLIPSE_HOME/$eclipse \
    -nosplash -application org.eclipse.ant.core.antRunner \
    --launcher.suppressErrors \
    -buildfile mkweb.xml      \
    -verbose \
    -Dos=$os -Dws=$ws -Darch=x86_64 $extra_defs mk_html

