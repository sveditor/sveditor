#!/bin/sh
#****************************************************************************
#* upload_release.sh
#****************************************************************************

version=$1

# Copy the new update site XML
scp update_tmp/site.xml $SF_USERNAME,sveditor@web.sourceforge.net:htdocs/update


sftp -b /dev/stdin $SF_USERNAME,sveditor@frs.sourceforge.net << EOF
cd /home/frs/project/s/sv/sveditor
mkdir update_site
cd update_site
mkdir $version
mkdir $version/plugins
mkdir $version/features

cd $version/features
put update_tmp/features/net.sf.sveditor_${version}.jar

cd ../plugins
put update_tmp/plugins/net.sf.sveditor.core_${version}.jar
put update_tmp/plugins/net.sf.sveditor.ui_${version}.jar
put update_tmp/plugins/net.sf.sveditor.libs.ovm_${version}.jar

cd ../../..

cd sveditor
put sveditor-${version}.jar
put sveditor-src-${version}.jar

EOF

