#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

use IO::File;

scenarios(dist => 1);

my $root = "..";
my $Debug;

if (!-r "$root/.git") {
    skip("Not in a git repository");
} else {
    ### Must trim output before and after our file list
    my $files = `cd $root && git ls-files --exclude-standard`;
    print "ST $files\n" if $Debug;
    $files =~ s/\s+/ /g;
    my $cmd = "cd $root && grep -n -P '(FIX"."ME|BO"."ZO)' $files | sort";
    my $grep = `$cmd`;
    print "$grep\n";
    if ($grep ne "") {
        my %names;
        foreach my $line (split /\n/, $grep) {
            $names{$1} = 1 if $line =~ /^([^:]+)/;
        }
        error("Files with FIX"."MEs: ",join(' ',sort keys %names));
    }
}

ok(1);
1;
