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

if (!-r "$root/.git") {
    $Self->skip("Not in a git repository");
} else {
    ### Must trim output before and after our file list
    my $status = `cd $root && git ls-files -o --exclude-standard`;
    print "ST $status\n" if $Debug;
    my %warns;
    foreach my $file (sort split /\n/, $status) {
	next if $file =~ /nodist/;
	$warns{$file} = "File not in git or .gitignore: $file";
    }
    if (keys %warns) {
	# First warning lists everything as that's shown in the driver summary
	$Self->error("Files untracked in git or .gitignore: ",join(' ',sort keys %warns));
	foreach my $file (sort keys %warns) {
	    $Self->error($warns{$file});
	}
    }
}

ok(1);
1;
