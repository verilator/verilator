#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.

my $root = "..";
my $Debug;

### Must trim output before and after our file list
`cd $root && make dist-file-list`;
my $manifest_files = `cd $root && make dist-file-list`;
$manifest_files =~ s!.*begin-dist-file-list:!!sg;
$manifest_files =~ s!end-dist-file-list:.*$!!sg;
print "MF $manifest_files\n";
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

my %file_regexps;
my $skip = file_contents("$root/MANIFEST.SKIP");
foreach my $file (sort keys %files) {
    foreach my $skip (split /\s+/,$skip) {
	if ($file =~ /$skip/) {
	    $files{$file} |= 4;
	    $file_regexps{$file} = $skip;
	}
    }
}

my %warns;
foreach my $file (sort keys %files) {
    my $tar = $files{$file}&1;
    my $dir = $files{$file}&2;
    my $skip = $files{$file}&4;

    print +(($tar ? "TAR ":"    ")
	    .($dir ? "DIR ":"    ")
	    .($skip ? "SKIP ":"     ")
	    ."  $file\n") if $Debug;

    if ($dir && !$tar && !$skip) {
	$warns{$file} = "File not in manifest or MANIFEST.SKIP: $file";
    } elsif (!$dir && $tar && !$skip) {
	$warns{$file} = "File in manifest, but not directory: $file";
    } elsif ($dir && $tar && $skip) {
	$warns{$file} = "File in manifest and also MANIFEST.SKIP, too general skip regexp '$file_regexps{$file}'?: $file";
    }
}

if (keys %warns) {
    # First warning lists everything as that's shown in the driver summary
    $Self->error("Files mismatch with manifest: ",join(' ',sort keys %warns));
    foreach my $file (sort keys %warns) {
	$Self->error($warns{$file});
    }
}

ok(1);
1;
