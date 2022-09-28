#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2019 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(simulator => 1);

top_filename("t/t_flag_main.v");

if (!$Self->have_coroutines) {
    skip("No coroutine support");
}
else {
    compile(
        verilator_flags => [# Custom as don't want -cc
                            "-Mdir $Self->{obj_dir}",
                            "--debug-check", ],
        verilator_flags2 => ['--binary'],
        verilator_make_cmake => 0,
        verilator_make_gmake => 0,
        make_main => 0,
        );

    execute(
        check_finished => 1,
        );
}

ok(1);
1;
