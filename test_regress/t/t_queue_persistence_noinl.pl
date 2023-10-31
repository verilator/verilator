#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2023 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(simulator => 1);

top_filename("t/t_queue_persistence.v");

if (!$Self->have_coroutines) {
    skip("No coroutine support");
}
else {
    compile(
        timing_loop => 1,
        verilator_flags2 => ["--timing --fno-inline +define+TEST_NOINLINE"],
        );

    execute(
        check_finished => 1,
        );
}

ok(1);
1;
