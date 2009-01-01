#!/bin/sh

. ./sveditor.info

top=`pwd`

if test ! -d ./update/plugins || ! -d ./update/feature; then
    echo "[ERROR] sveditor not built
    exit 1
fi

cd update
zip -r "$top/sveditor-${version}" features plugins site.xml

