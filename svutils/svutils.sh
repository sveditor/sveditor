#!/bin/sh

# First, find the installation path
if test -f $0; then
  svutils_instdir=`dirname $0`
  svutils_instdir=`cd $svutils_instdir; pwd`
  svutils_instdir=`dirname $svutils_instdir`
else
  # It must be in the path
  for path_elem in `echo $PATH | sed -e 's/:/ /g'`; do
    path_elem="${path_elem}/${0}"
    if test -f $path_elem; then
      svutils_instdir=`dirname $path_elem`
      svutils_instdir=`cd $svutils_instdir; pwd`
	  svutils_instdir=`dirname $svutils_instdir`
      break
    fi
  done
fi


uname_o=`uname -o`

if test "$uname_o" = "Cygwin"; then
  # Must change the path a bit
  svutils_instdir=`cygpath -w $svutils_instdir | sed -e 's%\\\\%/%g'`
fi

# Now, find Java
if test "$uname_o" = "Cygwin"; then
  java_key="HKLM\\SOFTWARE\\JavaSoft\\Java Runtime Environment"
  java_version=`reg query "$java_key" /v "CurrentVersion" | grep CurrentVersion | sed -e 's/^.*REG_SZ[ 	]*\([0-9][0-9\.]*\).*$/\1/'`
  java_home=`reg query "${java_key}\\\\${java_version}" /v "JavaHome" | grep JavaHome| sed  -e 's%\\\\%/%g' -e 's%^.*REG_SZ[ 	]*\([a-zA-Z].*$\)%\1%'`
  jvm="${java_home}/bin/java"
else  
  jvm=java
fi

echo "svutils_instdir=$svutils_instdir"
echo "jvm=$jvm"

# Finally, launch Java
"$jvm" -classpath $svutils_instdir/lib/svutils.jar net.sf.sveditor.svutils.SVUtils ${1+"$@"}

