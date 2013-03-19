#!/bin/sh
#****************************************************************************
#* sve_collect_compiler_args
#*
#* Root script that invokes the compile command
#****************************************************************************

# Locate directory where the root script is
if test -f $0; then
	sve_compiler_wrappers_dir=`dirname $0`
	sve_compiler_wrappers_dir=`cd $sve_compiler_wrappers_dir ; pwd`
else
	sve_collect_compiler_args=`which $0`
	if test ! -f $sve_collect_compiler_args; then
		echo "[ERROR] Failed to locate $0"
		exit 1
	fi
	sve_compiler_wrappers_dir=`dirname $sve_collect_compiler_args`
fi

# Ensure that the 'wrapper' compiler scripts are found
export PATH=${sve_compiler_wrappers_dir}:${PATH}


#get_out_file()
#{
#	outfile=""
#	while test -n "$1"; do
#		if test "$1" = "-o"; then
#			shift
#			outfile="$1"
#		fi
#		shift
#	done
#	echo $outfile
#}

#SVE_COMPILER_ARGS_FILE=`get_out_file ${1+"$@"}`

if test "x$SVE_COMPILER_ARGS_FILE" = "x"; then
	SVE_COMPILER_ARGS_FILE="sve_compiler_args.f"
fi

outdir=`dirname $SVE_COMPILER_ARGS_FILE`
outdir=`cd $outdir; pwd`
outfile=`basename $SVE_COMPILER_ARGS_FILE`

export SVE_COMPILER_ARGS_FILE=${outdir}/${outfile}

# Null out the file
echo "[NOTE] Writing compiler files to $SVE_COMPILER_ARGS_FILE"
echo "" > $SVE_COMPILER_ARGS_FILE

if test $? -ne 0; then
  echo "[ERROR] Failed to clear $SVE_COMPILER_ARGS_FILE"
  exit 1
fi

# Finally, execute the target command
exec ${1+"$@"}
