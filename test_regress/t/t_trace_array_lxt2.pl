#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003-2009 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.

scenarios(vlt => 1);

top_filename("t/t_trace_array.v");

compile(
    verilator_flags2 => ['--cc --trace-lxt2 --trace-structs'],
    );

execute(
    check_finished => 1,
    );

lxt2vcd($Self->trace_filename, "$Self->{obj_dir}/simx-lxt2vcd.vcd");
vcd_identical("$Self->{obj_dir}/simx-lxt2vcd.vcd", "t/$Self->{name}.out");

ok(1);
1;
