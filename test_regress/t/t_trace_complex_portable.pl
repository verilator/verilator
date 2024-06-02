#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003-2009 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

# Same test as t_trace_complex, but exercising the old VCD tracing API

scenarios(vlt => 1);

top_filename("t/t_trace_complex.v");
golden_filename("t/t_trace_complex.out");

compile(
    verilator_flags2 => ['--cc --trace -CFLAGS -DVL_PORTABLE_ONLY'],
    );

execute(
    check_finished => 1,
    );

file_grep("$Self->{obj_dir}/simx.vcd", qr/ v_strp /);
file_grep("$Self->{obj_dir}/simx.vcd", qr/ v_strp_strp /);
file_grep("$Self->{obj_dir}/simx.vcd", qr/ v_arrp /);
file_grep("$Self->{obj_dir}/simx.vcd", qr/ v_arrp_arrp /);
file_grep("$Self->{obj_dir}/simx.vcd", qr/ v_arrp_strp /);
file_grep("$Self->{obj_dir}/simx.vcd", qr/ v_arru\[/);
file_grep("$Self->{obj_dir}/simx.vcd", qr/ v_arru_arru\[/);
file_grep("$Self->{obj_dir}/simx.vcd", qr/ v_arru_arrp\[/);
file_grep("$Self->{obj_dir}/simx.vcd", qr/ v_arru_strp\[/);

vcd_identical("$Self->{obj_dir}/simx.vcd", $Self->{golden_filename});

ok(1);
1;
