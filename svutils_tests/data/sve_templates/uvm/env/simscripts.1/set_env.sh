#****************************************************************************
#* simscripts set_env.sh
#****************************************************************************

rootdir=`pwd`

while test "x$rootdir" != "x"; do
  runtest=`find $rootdir -maxdepth 4 -name runtest.pl` 
  if test "x$runtest" != "x"; then
    break;
  fi
  rootdir=`dirname $rootdir`
done


if test "x$runtest" = "x"; then
  echo "Error: Failed to find root directory"
else
  n_runtest=`echo $runtest | wc -w`
  if test $n_runtest -gt 1; then
    echo "Note: found multiple runtest.pl scripts: $runtest"
    for rt in $runtest; do
      rt_dir=`dirname $rt`
      rt_dir=`dirname $rt_dir`
      if test -d $rt_dir/mkfiles; then
        echo "Note: selecting $rt"
        real_rt=$rt
        break
      fi
    done
    runtest=$real_rt
  fi
   
  if test "x$runtest" = "x"; then
    echo "Error: Failed to disambiguate runtest.pl"
  else
    SIMSCRIPTS_DIR=`dirname $runtest`
    export SIMSCRIPTS_DIR=`dirname $SIMSCRIPTS_DIR`
    echo "SIMSCRIPTS_DIR=$SIMSCRIPTS_DIR"
    # TODO: check whether the PATH already contains the in directory
    PATH=${SIMSCRIPTS_DIR}/bin:$PATH


    # Environment-specific variables
    if test -f $SIMSCRIPTS_DIR/../env/env.sh; then
        . $SIMSCRIPTS_DIR/../env/env.sh
    fi
  fi
fi




