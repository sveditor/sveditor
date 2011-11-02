#!/usr/bin/perl

use Cwd;

$add=1;
$force=0;

$top=getcwd();

open(FL, "find -name '*.java' |");

while (($filename=<FL>)) {
    chomp($filename);

    open(FH, $filename);
    
    $i=0;
    $found=0;
    while (($line=<FH>) && $i++ < 50) {
        chomp($line);
        if ($line =~ m/Copyright/ &&
            $line =~ m/Matthew Ballance/) {
            $found = 1;
            last;
        }
    }

    if ($found) {
        print "[NOTE] $filename has a copyright\n";
        if ($force) {
        }
    } else {
        if ($add) {
            print "[NOTE] Adding a copyright to $filename\n";
            close(FH);
            open(FH, $filename);
            open(FHN, ">${filename}.new");
            open(TMPL, "etc/copyright_java.txt");

            while (($line=<TMPL>)) {
                print FHN $line;
            }
            close(TMPL);
            while (($line=<FH>)) {
                print FHN $line;
            }
            close(FHN);
            close(FH);

            system("mv ${filename}.new ${filename}");
        } else {
            print "[NOTE] $filename does not have a copyright\n";
            close(FH);
        }
    }
}



