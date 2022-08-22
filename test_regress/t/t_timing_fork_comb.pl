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
}
else {
    # Should convert the first always into combo and detect cycle
    compile(
        fails => 1,
        verilator_flags2 => ["--timing"],
        expect =>
            '%Warning-UNOPTFLAT: t/t_timing_fork_comb.v:\d+:\d+: Signal unoptimizable: Circular combinational logic:'
        );

    compile(
        verilator_flags2 => ["--exe --main --timing -Wno-UNOPTFLAT"],
        make_main => 0,
        );

    execute(
        check_finished => 1,
        );
}

ok(1);
1;
