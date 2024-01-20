#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2022 by Antmicro Ltd. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(simulator => 1);

$Self->{main_time_multiplier} = 10e-7 / 10e-9;

top_filename("t/t_delay_incr.v");

compile(
    timing_loop => 1,
    verilator_flags2 => ['--binary --timing -Wno-ZERODLY'],
    );

execute(
    check_finished => 1,
    );

ok(1);
1;
