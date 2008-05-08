#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("./driver.pl", @ARGV, $0); die; }
# $Id$
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# General Public License or the Perl Artistic License.

my $root = "..";
my $Debug;

###
# Call once and ignore to rebuild any targets before we need the output
`cd $root && make dist-file-list`;
my $manifest_files = `cd $root && make dist-file-list`;
$manifest_files =~ s!.*dist-file-list:!!sg;
my %files;
foreach my $file (split /\s+/,$manifest_files) {
    next if $file eq '';
    $files{$file} |= 1;
}

my $all_files = `cd $root && find . -type f -print`;
foreach my $file (split /\s+/,$all_files) {
    next if $file eq '';
    $file =~ s!^\./!!;
    $files{$file} |= 2;
}

my $skip = file_contents("$root/MANIFEST.SKIP");
foreach my $file (sort keys %files) {
    foreach my $skip (split /\s+/,$skip) {
	if ($file =~ /$skip/) {
	    $files{$file} |= 4;
	}
    }
}

foreach my $file (sort keys %files) {
    my $tar = $files{$file}&1;
    my $dir = $files{$file}&2;
    my $skip = $files{$file}&4;

    print +(($tar ? "TAR ":"    ")
	    .($dir ? "DIR ":"    ")
	    .($skip ? "SKIP ":"     ")
	    ."  $file\n") if $Debug;

    if ($dir && !$tar && !$skip) {
	$Last_Self->error("File not in manifest or MANIFEST.SKIP: $file");
    } elsif (!$dir && $tar && !$skip) {
	$Last_Self->error("File in manifest, but not directory: $file");
    }
}

ok(1);
1;
