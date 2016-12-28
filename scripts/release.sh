#!/bin/sh

is_mingw=`uname | sed -e 's/MINGW.*$/1/'`
is_cygwin=`uname | sed -e 's/CYGWIN.*$/1/'`
u_arch=`uname -m`

if test "$is_mingw" = "1" || test "$is_cygwin" = "1"; then
  os=win32
  ws=win32
  arch=x86_64
  eclipse=eclipsec
else
  os=linux
  ws=gtk
  if test $u_arch = "x86_64"; then
    arch=x86_64
  else
    arch=x86
  fi
  eclipse=eclipse
fi

if test "$is_cygwin" = "1"; then
  export ECLIPSE_HOME=`cygpath -w $ECLIPSE_HOME | sed -e 's%\\\\%/%g'`
fi

$ECLIPSE_HOME/${eclipse} \
    -nosplash -application org.eclipse.ant.core.antRunner \
    --launcher.suppressErrors   \
    -buildfile release.xml      \
    -Dos=${os} -Dws=${ws} -Darch=${arch} -verbose release


