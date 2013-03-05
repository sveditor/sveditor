#!/bin/sh

scp -C -r html2/*.html html2/imgs \
  mballance,sveditor@web.sourceforge.net:htdocs

