#!/bin/sh

$ECLIPSE_HOME/eclipse \
    -nosplash -application org.eclipse.ant.core.antRunner \
    --launcher.suppressErrors \
    -buildfile build.xml      \
    -Dos=linux -Dws=gtk -Darch=x86_64 build

