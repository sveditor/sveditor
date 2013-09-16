#!/bin/sh
#****************************************************************************
#* mksrc.sh
#*
#* Create a source .zip file 
#****************************************************************************

top=`pwd`

. ../etc/sveditor.info


mkdir "$top/../sveditor-src-${version}"
cd "$top/../sveditor-src-${version}"

cp -r \
  $top/../sveditor \
  $top/../sve      \
  $top/../etc      \
  $top/../scripts  \
  .

# Remove .svn directories
rm -rf `find -name '.git' -print`
rm -rf `find -name 'bin' -print`
rm -rf `find -name 'class' -print`

cd $top/..
zip -r "sveditor-src-${version}.zip" sveditor-src-${version}

rm -rf sveditor-src-${version}

