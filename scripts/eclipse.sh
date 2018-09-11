#!/bin/sh

echo "ECLIPSE_HOME=$ECLIPSE_HOME"
uname_o=`uname -o`
launcher_jar=`ls ${ECLIPSE_HOME}/plugins/org.eclipse.equinox.launcher_*.jar`
if test "Cygwin" = "$uname_o"; then
  launcher_jar=`cygpath -w $launcher_jar | sed -e 's%\\\\%/%g'`
fi

echo "launcher_jar=$launcher_jar"

# java -jar $launcher_jar ${@+1}
java -jar $launcher_jar $*

