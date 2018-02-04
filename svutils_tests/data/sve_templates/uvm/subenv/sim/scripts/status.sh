#!/bin/sh

testname=$1

if test ! -f simx.log; then
  echo "FAIL: $testname - no log file"
else
  n_fails=`grep "FAIL: $testname" simx.log | wc -l`
  n_pass=`grep "PASS: $testname" simx.log  | wc -l`

  if test $n_fails -gt 0; then
    echo "FAIL: $testname"
  elif test $n_pass -gt 0; then
    echo "PASS: $testname"
  else
    echo "FAIL: $testname - no PASS or FAIL"
  fi
fi
