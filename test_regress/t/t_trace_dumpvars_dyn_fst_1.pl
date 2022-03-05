#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003-2009 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(vlt_all => 1);

top_filename("t_trace_dumpvars_dyn.v");

compile(
    make_main => 0,
    verilator_flags2 => ["--trace-fst --exe $Self->{t_dir}/t_trace_dumpvars_dyn.cpp"],
    );

execute(
    check_finished => 1,
    );

fst_identical("$Self->{obj_dir}/simx.vcd", $Self->{golden_filename});

ok(1);
1;
