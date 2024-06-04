#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(simulator => 1);

top_filename("t/t_hier_trace.v");

compile(
    verilator_flags2 => ['--trace', '-j 4', 't/t_hier_trace_sub/t_hier_trace.vlt', '--top-module t', '--hierarchical', '--fno-inline', '-F t/t_hier_trace_sub/top.F'],
    );

execute(
    all_run_flags => ['-j 4'],
    check_finished => 1,
    );

vcd_identical("$Self->{obj_dir}/simx.vcd", $Self->{golden_filename});

ok(1);
1;
