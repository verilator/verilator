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

top_filename("t/t_trace_cat.v");

compile(
    make_top_shell => 0,
    make_main => 0,
    v_flags2 => ["--trace --exe $Self->{t_dir}/t_trace_cat.cpp"],
    );

execute(
    check_finished => 1,
    );

vcd_identical("$Self->{obj_dir}/simpart_0000.vcd",
              "t/$Self->{name}_0000.out");
vcd_identical("$Self->{obj_dir}/simpart_0100.vcd",
              "t/$Self->{name}_0100.out");

ok(1);
1;
