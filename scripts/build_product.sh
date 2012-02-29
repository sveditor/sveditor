#!/bin/sh

$ECLIPSE_HOME/eclipse \
    -nosplash -application org.eclipse.ant.core.antRunner \
    --launcher.suppressErrors \
    -buildfile mk_product.xml      \
    -Dos=linux mk_product

