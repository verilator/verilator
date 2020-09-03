#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(simulator_st => 1);

top_filename("t/t_time_vpi.v");

$Self->{main_time_multiplier} = 1e-6 / 1e-9;

compile(
    v_flags2 => ['+define+time_scale_units=1us +define+time_scale_prec=1ns',
                 't/t_time_vpi_c.cpp'],
    verilator_flags2 => ['--vpi'],
    );

execute(
    check_finished => 1,
    expect_filename => $Self->{golden_filename},
    );

ok(1);

1;
