#!/bin/sh

. $INFACT_HOME/etc/infact_setup.sh

CWD=`pwd`
PROJECT_LOC=`dirname $CWD`
export PROJECT_LOC

vsim -c -do "run -all ; quit -f" \
  -sv_lib $INFACT_LIBDIR/libinFactSysV \
  +infact=${PROJECT_LOC}/infact/infact.ini \
  +UVM_TESTNAME=multi_port_shared_cov_env \
  \
  multi_port_shared_cov_tb
  