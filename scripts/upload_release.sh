#!/bin/sh
#****************************************************************************
#* upload_release.sh
#****************************************************************************
. sveditor.info

echo "Beginning release of $version" > release/release.log

sftp_cmd="sftp -b /dev/stdin $SF_USERNAME,sveditor@frs.sourceforge.net"

# Copy the update site XML down for modification
scp $SF_USERNAME,sveditor@web.sourceforge.net:htdocs/update/site.xml \
    release/site_ex.xml >> release/release.log 2>&1 

if test ! -f release/site_ex.xml; then
    echo "[ERROR] failed to download existing site.xml"
    exit 1
fi

# Add the new release
./scripts/add_release.pl \
    release/site_ex.xml \
    release/new_release_fragment.xml $version > release/site.xml

scp release/site.xml \
    $SF_USERNAME,sveditor@web.sourceforge.net:htdocs/update/site.xml \
    >> release/release.log 2>&1

update_site=./release/update_site

./scripts/mk_rn.pl $version > release/rn.txt

mkdir update_site

sveditor_dir=/home/frs/project/s/sv/sveditor

sftp -b /dev/stdin $SF_USERNAME,sveditor@frs.sourceforge.net << EOF
    cd $sveditor_dir
    -mkdir update_site
    cd update_site
    -mkdir $version
    cd $version
    -mkdir plugins
    -mkdir features

    cd $sveditor_dir/sveditor
    -mkdir $version

    cd $sveditor_dir/update_site
    cd $version/features
    put $update_site/features/net.sf.sveditor_${version}.jar

    cd ../plugins
    put $update_site/plugins/net.sf.sveditor.core_${version}.jar
    put $update_site/plugins/net.sf.sveditor.ui_${version}.jar
    put $update_site/plugins/net.sf.sveditor.libs.ovm_${version}.jar

    cd ../../..

    cd sveditor
    cd $version
    put sveditor-${version}.jar
    put sveditor-src-${version}.zip
    put release/rn.txt
EOF



