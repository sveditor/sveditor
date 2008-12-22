#!/bin/sh

top=`pwd`

. ./sveditor.info


mkdir "$top/sveditor-src-${version}"
cd "$top/sveditor-src-${version}"

cp -r $top/plugins $top/features $top/ChangeLog.txt .

# Remove .svn directories
rm -rf `find -name '.svn' -print`

cd $top
zip -r "sveditor-src-${version}.zip" sveditor-src-${version}

rm -rf sveditor-src-${version}

