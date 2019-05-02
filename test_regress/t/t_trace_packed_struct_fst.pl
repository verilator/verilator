#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.

scenarios(simulator => 1);

top_filename("t/t_trace_packed_struct.v");

compile(
    v_flags2 => ["--trace-fst"]
    );

execute(
    check_finished => 1,
    );

fst2vcd($Self->trace_filename, "$Self->{obj_dir}/simx-fst2vcd.vcd");
vcd_identical("$Self->{obj_dir}/simx-fst2vcd.vcd", $Self->{golden_filename});

ok(1);
1;
