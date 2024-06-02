#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2022 by Antmicro Ltd. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(vlt_all => 1);

top_filename("t/t_timing_sched.v");

compile(
    verilator_flags2 => ["--exe --main --timing"],
    );

execute(
    all_run_flags => ["+verilator+debug"],
    check_finished => 1,
    );

if (!$Self->{vltmt}) {  # vltmt output may vary between thread exec order
    files_identical("$Self->{obj_dir}/vlt_sim.log", $Self->{golden_filename}, "logfile");
}

ok(1);
1;
