#!/bin/sh

uname_o=`uname -o`

if test "$uname_o" = "Cygwin"; then
CC=i686-pc-mingw32-gcc
else
CC=gcc
fi

echo "$CC -o wrapper.exe wrapper.c"
$CC -o wrapper.exe wrapper.c
echo "$CC -o sve_collect_compiler_args.exe sve_collect_compiler_args.c"
$CC -o sve_collect_compiler_args.exe sve_collect_compiler_args.c

