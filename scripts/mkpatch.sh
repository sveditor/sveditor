#!/bin/sh

tree_1="$1"
tree_2="$2"

if test ! -f $tree_1/ChangeLog.txt; then
   echo "[ERROR] $tree_1 does not contain ChangeLog.txt"
   echo "[ERROR] Unlikely to be a correct SVEditor tree"
fi

if test ! -f $tree_2/ChangeLog.txt; then
   echo "[ERROR] $tree_2 does not contain ChangeLog.txt"
   echo "[ERROR] Unlikely to be a correct SVEditor tree"
fi


diff -rcNB \
    -x '*.class' -x '.svn' -x '.svproject' -x 'toc.xml' \
    -x '*_toc.xml' -x '*-toc.xml' -x 'api_docs' \
    -x 'SVUIResources.properties' -x '*.html' \
    $tree_1 $tree_2

