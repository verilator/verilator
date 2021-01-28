#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003-2009 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(simulator => 1);

top_filename("t/t_interface_ref_trace.v");
golden_filename("t/t_interface_ref_trace.out");

compile(
    v_flags2 => ['+define+NO_INLINE_A'],
    verilator_flags2 => ['--trace-structs --trace'],
    );

execute(
    check_finished => 1,
    );

vcd_identical($Self->trace_filename,
              $Self->{golden_filename});

ok(1);
1;
