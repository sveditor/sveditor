#!/usr/bin/perl
#****************************************************************************
#* add_release.pl
#*
#* Processes an existing site.xml file and merges information for a new
#* release
#*
#* add_release.pl <existing site.xml> <release info fragment> <version>
#****************************************************************************


open(FH, $ARGV[0]) || die "Cannot open file $ARGV[0]";
$etc_dir=$ARGV[1];
$new_release_fragment=$ARGV[2];
$version=$ARGV[3];
open(FR, $new_release_fragment) || die "Cannot open new_release_fragment.xml file $new_release_fragment";

$site_head="$etc_dir/site_head.xml";
$site_tail="$etc_dir/site_tail.xml";

$do_output=1;

@sections = ("", "", "");

$section="";
while (<FH>) {
    $line = $_;
    chomp $line;

    if ($line =~ m/BEGIN: Release $version/) {
        # site file already contains this release
        # skip lines until the END token
        $do_output=0;
    }

    if ($line =~ m/END: Release $version/) {
        # Reached the end of the existing release
        $do_output=1;
    }
}

while (<FH>) {
    $line = $_;
    chomp $line;

    if ($line =~ m/category-def/) {
        # insert the new content
        while (<FR>) {
            print "$_";
        }
        close(FR);
    }

    if ($line =~ m/BEGIN: Release $version/) {
        # site file already contains this release
        # skip lines until the END token
        $do_output=0;
    }

    if ($do_output == 1) {
        print "$line\n";
    }

    if ($line =~ m/END: Release $version/) {
        # Reached the end of the existing release
        $do_output=1;
    }
}


close(FH);

