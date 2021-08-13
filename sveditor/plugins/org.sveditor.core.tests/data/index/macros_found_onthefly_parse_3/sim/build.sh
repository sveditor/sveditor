#!/bin/sh

. $INFACT_HOME/etc/infact_setup.sh

CWD=`pwd`
PROJECT_LOC=`dirname $CWD`
export PROJECT_LOC

$INFACT_HOME/bin/infact cmd genproject ${PROJECT_LOC}/infact

vlib work

vlog -sv $INFACT_HOME/include/inFactSvPackage.sv \
  -f ${PROJECT_LOC}/sv/sv.f \
  -f ${PROJECT_LOC}/tb/tb.f

  
