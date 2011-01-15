#!/usr/bin/perl
#****************************************************************************
#* mk_rn.pl
#*
#* Create the release notes from the Changelog
#****************************************************************************


open(FH, "ChangeLog.txt") || die "Cannot open ChangeLog.txt";
$version=$ARGV[0];

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


