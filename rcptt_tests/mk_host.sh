#!/bin/sh

extra_defs=""

while test -n "$1"; do
  case $1 in
    -D*)
      extra_defs="$extra_defs $1"
      ;;
    -*)
      echo "[ERROR] Unknown option $1"
      ;;
    *)
      echo "[ERROR] Unknown argument $1"
      ;;
  esac
  shift
done

is_mingw=`uname | sed -e 's/MINGW.*$/1/'`
is_cygwin=`uname | sed -e 's/CYGWIN.*$/1/'`
u_arch=`uname -m`

if test "$u_arch" = "x86_64"; then
  arch=x86_64
else
  arch=i386
fi

if test "$is_mingw" = "1" || test "$is_cygwin" = "1"; then
  os=win32
  ws=win32
  eclipse=eclipsec
else
  os=linux
  ws=gtk
  eclipse=eclipse
fi

if test "$is_cygwin" = "1"; then
  export ECLIPSE_HOME=`cygpath -w $ECLIPSE_HOME | sed -e 's%\\\\%/%g'`
fi

verbose=""
#verbose="-verbose"

echo "os=$os ws=$ws arch=$arch"

$ECLIPSE_HOME/$eclipse \
    -nosplash -application org.eclipse.ant.core.antRunner \
    --launcher.suppressErrors \
    -buildfile mk_host.xml      \
    ${verbose} \
    -Dos=$os -Dws=$ws -Darch=$arch $extra_defs mk_host

