#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003-2013 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(vlt_all => 1);

top_filename("t_trace_cat.v");

compile(
    make_top_shell => 0,
    make_main => 0,
    v_flags2 => ["--trace --no-trace-top --exe $Self->{t_dir}/t_no_trace_top.cpp"],
    );

execute(
    check_finished => 1,
    );

vcd_identical("$Self->{obj_dir}/simno_trace_top.vcd",
              $Self->{golden_filename});

ok(1);
1;
