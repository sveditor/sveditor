#!/bin/sh

echo "ECLIPSE_HOME=$ECLIPSE_HOME"
launcher_jar=`ls ${ECLIPSE_HOME}/plugins/org.eclipse.equinox.launcher_*.jar`
launcher_jar=`cygpath -w $launcher_jar | sed -e 's%\\\\%/%g'`

echo "launcher_jar=$launcher_jar"

# java -jar $launcher_jar ${@+1}
java -jar $launcher_jar $*

