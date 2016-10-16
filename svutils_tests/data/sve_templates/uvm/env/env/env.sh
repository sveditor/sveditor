
export ${name_uc}_ROOT=`dirname ${SIMSCRIPTS_DIR}`

uname_o=`uname -o`

if test "$uname_o" = "Cygwin"; then
	${name_uc}_ROOT=`cygpath -w ${name_uc}_ROOT | sed -e 's%\\\\%/%g'`
fi


