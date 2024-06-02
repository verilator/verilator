#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2022 by Geza Lore. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(vlt_all => 1);

top_filename("t/t_merge_cond.v");

compile(
    verilator_flags2 => ["-unroll-count 64", "--stats", "-fno-merge-cond-motion"],
    );

execute(
    check_finished => 1,
    );

if ($Self->{vlt}) {
    # Note, with vltmt this might be split differently, so only checking vlt
    file_grep($Self->{stats}, qr/Optimizations, MergeCond merges\s+(\d+)/i,
              10);
    file_grep($Self->{stats}, qr/Optimizations, MergeCond merged items\s+(\d+)/i,
              580);
    file_grep($Self->{stats}, qr/Optimizations, MergeCond longest merge\s+(\d+)/i,
              64);
}

ok(1);
1;
