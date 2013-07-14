#!/bin/sh

scp -C -r html/*.html html/imgs \
  mballance,sveditor@web.sourceforge.net:htdocs

