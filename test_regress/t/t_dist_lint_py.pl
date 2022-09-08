#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2022 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(dist => 1);

my $root = "..";

if (!-r "$root/.git") {
    skip("Not in a git repository");
} else {
    my $cmd = "cd $root && make lint-py";
    my $out = `$cmd`;
    my $first;
    foreach my $line (split /\n+/, $out) {
        next if $line =~ /^---/;
        next if $line =~ /^flake8/;
        next if $line =~ /^pylint/;
        print "$line\n";
        if (!defined $first) {
            $first = $line;
            error("lint-py failed: ", $first);
        }
    }
}

ok(1);
1;
