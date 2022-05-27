#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2022 by Geza Lore. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(vlt => 1);

# TODO: This takes excessively long on vltmt, this should be fixed

compile(
    verilator_flags2 => ["--unroll-count 1000000000", "--output-split 0", "--stats"],
    );

execute(
    check_finished => 1,
    );

if ($Self->{vlt}) {
    # Note, with vltmt this might be split differently, so only checking vlt
    file_grep($Self->{stats}, qr/Optimizations, MergeCond merges\s+(\d+)/i,
              500);   # V3MergeCond.cpp MAX_DISTANCE
    file_grep($Self->{stats}, qr/Optimizations, MergeCond merged items\s+(\d+)/i,
              1000);  # V3MergeCond.cpp MAX_DISTANCE *2
    file_grep($Self->{stats}, qr/Optimizations, MergeCond longest merge\s+(\d+)/i,
              2);
}

ok(1);
1;
