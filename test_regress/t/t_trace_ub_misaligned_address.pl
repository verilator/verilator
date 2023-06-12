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

if (!$Self->have_coroutines) {
    skip("No coroutine support");
}
else {
    top_filename("t/t_trace_ub_misaligned_address.v");

    compile(
        verilator_flags2 => ["--binary --timing --trace",
                             "-CFLAGS -fsanitize=address,undefined",
                             "-LDFLAGS -fsanitize=address,undefined"],
        verilator_make_cmake => 0,
        verilator_make_gmake => 0,
        make_main => 0,
        );

    execute(
        check_finished => 1,
        );

# Make sure that there are no additional messages (such as runtime messages
# regarding undefined behavior).
    files_identical("$Self->{obj_dir}/vlt_sim.log", $Self->{golden_filename}, "logfile");
}

ok(1);
1;
