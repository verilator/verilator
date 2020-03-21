#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(simulator => 1);

compile(
    verilator_flags2 => ["-unroll-count 1024",
                         $Self->wno_unopthreads_for_few_cores(),
                         "--stats"],
    );

execute(
    check_finished => 1,
    );

if ($Self->{vlt_all}) {
    file_grep($Self->{stats}, qr/Optimizations, Reloop iterations\s+(\d+)/i,
              768);
    file_grep($Self->{stats}, qr/Optimizations, Reloops\s+(\d+)/i,
              3);
}

ok(1);
1;
