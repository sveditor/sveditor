#!/bin/sh
#****************************************************************************
#* vlog
#*
#* Wrapper for 'vlog' to allow arguments to be intercepted and collected
#* in a file
#****************************************************************************

if test "x$SVE_COMPILER_ARGS_FILE" = "x"; then
	echo "[ERROR] SVE_COMPILER_ARGS_FILE not set"
	exit 1
fi

CWD=`pwd`

echo "/**" >> $SVE_COMPILER_ARGS_FILE
echo " * Invoking vlog in $CWD" >> $SVE_COMPILER_ARGS_FILE
echo " * vlog $*" >> $SVE_COMPILER_ARGS_FILE
echo " */" >> $SVE_COMPILER_ARGS_FILE


while test -n "$1"; do
	case "$1" in
		+incdir+*)
			dir=`echo $1 | sed -e 's/+incdir+//g'`
			if test -d "$dir"; then
				dir=`cd $dir; pwd`
			fi
			echo "+incdir+${dir}" >> $SVE_COMPILER_ARGS_FILE
		;;
		
		*)
		if test -f "$1"; then
			# Convert this to a full path
			filedir=`dirname "$1"`
			filename=`basename "$1"`
			filedir=`cd $filedir ; pwd`
			echo "${filedir}/${filename}" >> $SVE_COMPILER_ARGS_FILE
		else
			echo "$1" >> $SVE_COMPILER_ARGS_FILE
		fi
		;;
	esac
	shift
done

echo "" >> $SVE_COMPILER_ARGS_FILE
echo "" >> $SVE_COMPILER_ARGS_FILE
