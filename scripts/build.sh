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
    -buildfile build.xml      \
    -verbose \
    -Dos=$os -Dws=$ws -Darch=x86_64 $extra_defs build

