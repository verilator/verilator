#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

use IO::File;
use File::Spec::Functions 'catfile';

scenarios(dist => 1);

my $root = "..";
my $Debug;

if (!-r "$root/.git") {
    skip("Not in a git repository");
} else {
    ### Must trim output before and after our file list
    my $files = `cd $root && git ls-files --exclude-standard`;
    print "ST $files\n" if $Debug;
    my %names;

    $files =~ s/\s+/ /g;
    my @batch;
    my $n = 0;
    my $re = qr/(FIX[M]E|BO[Z]O)/;
    foreach my $file (split /\s+/, $files) {
        my $filename = catfile($root, $file);
        next if !-r $filename;
        my $wholefile = file_contents($filename);
        if ($wholefile =~ /$re/) {
            $names{$file} = 1;
        }
    }
    if (scalar(%names) >= 1) {
        error("Files with FIX" . "MEs: ", join(' ', sort keys %names));
    }
}

ok(1);
1;
