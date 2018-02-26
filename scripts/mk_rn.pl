#!/usr/bin/perl
#****************************************************************************
#* mk_rn.pl
#*
#* Create the release notes from the Changelog
#****************************************************************************

$version=$ARGV[0];
$changelog=$ARGV[1];

open(FH, "$changelog") || die "Cannot open ChangeLog.txt";

$do_output=0;

while (<FH>) {
    $line = $_;
    chomp $line;

    if ($line =~ m/-- $version Release --/) {
        $do_output=1;
    } elsif ($line =~ m/--------/) {
        $do_output=0;
    }

    if ($do_output == 1) {
       print("$line\n");
    }
}


