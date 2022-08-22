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

if (!$Self->have_coroutines) {
    skip("No coroutine support");
} elsif (!$Self->have_cmake) {
    skip("cmake is not installed");
} else {
    top_filename("t/t_timing_events.v");

    compile(
        verilator_flags2 => ["--timescale 10ns/1ns --main --timing"],
        verilator_make_gmake => 0,
        verilator_make_cmake => 1,
        );
}

ok(1);
1;
