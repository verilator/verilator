#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(vlt_all => 1);

compile(
    verilator_flags2 => ["-unroll-count 1", "--stats"],
    );

execute(
    check_finished => 1,
    );

file_grep($Self->{stats}, qr/Dynamic NBA, variables needing commit queue without partial updates\s+(\d+)/i,
          6);
file_grep($Self->{stats}, qr/Dynamic NBA, variables needing commit queue with partial updates\s+(\d+)/i,
          3);

ok(1);
1;
