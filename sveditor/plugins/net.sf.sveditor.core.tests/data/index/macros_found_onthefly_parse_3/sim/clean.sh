#!/bin/sh

. $INFACT_HOME/etc/infact_setup.sh

CWD=`pwd`
PROJECT_LOC=`dirname $CWD`
export PROJECT_LOC

$INFACT_HOME/bin/infact cmd cleanproject ${PROJECT_LOC}/infact

rm -rf work transcript

