#!/bin/sh

. ./sveditor.info

top=`pwd`

if test ! -d ./update/plugins || test ! -d ./update/features; then
    echo "[ERROR] sveditor not built"
    exit 1
fi

cd update
zip -r "$top/sveditor-${version}.zip" features plugins site.xml

