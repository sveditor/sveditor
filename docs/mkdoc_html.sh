#!/bin/sh

$ECLIPSE_HOME/eclipse \
    -nosplash -application org.eclipse.ant.core.antRunner \
    --launcher.suppressErrors \
    -buildfile mkdoc.xml      \
    -verbose \
    -Dos=linux -Dws=gtk -Darch=x86_64 $extra_defs mk_user_guide_html

