#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(vlt_all => 1);

top_filename("t/t_extract_static_const.v");
golden_filename("t/t_extract_static_const.out");

compile(
    verilator_flags2 => ["--stats", "--no-merge-const-pool"],
    );

execute(
    check_finished => 1,
    expect_filename => $Self->{golden_filename},
    );

if ($Self->{vlt_all}) {
    file_grep($Self->{stats}, qr/Optimizations, Prelim extracted value to ConstPool\s+(\d+)/i,
              8);
    file_grep($Self->{stats}, qr/ConstPool, Constants emitted\s+(\d+)/i,
              2);
}

ok(1);
1;
