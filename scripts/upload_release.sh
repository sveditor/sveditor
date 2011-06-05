#!/bin/sh
#****************************************************************************
#* upload_release.sh
#****************************************************************************
. sveditor.info

echo "Beginning release of $version" > release/release.log

sftp_cmd="sftp -b /dev/stdin $SF_USERNAME,sveditor@frs.sourceforge.net"

# Copy the update site XML down for modification
#scp "$update_site_url/site.xml" release/site_ex.xml >> release/release.log 2>&1

#if test ! -f release/site_ex.xml; then
#    echo "[ERROR] failed to download existing site.xml"
#    exit 1
#fi

# Add the new release
#./scripts/add_release.pl \
#    release/site_ex.xml \
#    release/new_release_fragment.xml $version > release/site.xml

cat ./etc/site_head.xml release/new_release_fragment.xml ./etc/site_tail.xml > release/site.xml
scp release/site.xml "$update_site_url/site.xml" >> release/release.log 2>&1

update_site=./release/update_site

./scripts/mk_rn.pl $version > release/rn.txt

mkdir update_site

sveditor_dir=/home/frs/project/s/sv/sveditor

sftp -b /dev/stdin $SF_USERNAME,sveditor@frs.sourceforge.net << EOF
    cd $sveditor_dir
    -mkdir $frs_update_site_dir
    cd $frs_update_site_dir
    -mkdir $version
    cd $version
    -mkdir plugins
    -mkdir features

    cd $sveditor_dir/sveditor
    -mkdir $version

    cd $sveditor_dir/$frs_update_site_dir
    cd $version/features
    put $update_site/features/net.sf.sveditor_${version}.jar

    cd ../plugins
    put $update_site/plugins/net.sf.sveditor.core_${version}.jar
    put $update_site/plugins/net.sf.sveditor.core.uvm.templates_${version}.jar
    put $update_site/plugins/net.sf.sveditor.ui_${version}.jar
    put $update_site/plugins/net.sf.sveditor.doc.user_${version}.jar
    put $update_site/plugins/net.sf.sveditor.doc.dev_${version}.jar

    cd ../../..

    cd sveditor
    cd $version
    put sveditor-${version}.jar
    put sveditor-src-${version}.zip
    put release/rn.txt
EOF


# Finally, update the release tag
if test $do_tag -eq 1; then
  svnroot="https://sveditor.svn.sourceforge.net/svnroot/sveditor"
  svn_cmd="svn --username $SF_USERNAME"

  # Check, first to see if we can access
  $svn_cmd ls $svnroot/$src_url > /dev/null

  if test $? -ne 0; then
    echo "[ERROR] cannot access SVNROOT"
    exit 1
  fi

  # Next, see if the release tag already exists
  $svn_cmd ls $svnroot/tags/release/${version} > /dev/null

  if test $? -eq 0; then
    # already exists. Deletes
    $svn_cmd rm -m "Cleanup for ${version} re-release" \
      $svnroot/tags/release/${version}
  fi

  # Finally, create the release tag
  $svn_cmd cp -m "Release tag for ${version}" \
     $svnroot/$src_url $svnroot/tags/release/${version}

  if test $? -ne 0; then
    echo "[ERROR] failed to create release tag"
    exit 1
  fi
fi #



