#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This file ONLY is placed under the Creative Commons Public Domain, for
# any use, without warranty, 2023 by Toru Niina.
# SPDX-License-Identifier: CC0-1.0


scenarios(vlt => 1);

if (!$Self->have_coroutines) {
    skip("No coroutine support")
}
else {
    compile(
        v_flags2 => ["t/t_timing_dpi.cpp"],
        verilator_flags2 => ["--exe --main --timing"],
        make_main => 0,
        );

    execute(
        check_finished => 1,
        );
}

ok(1);
1
