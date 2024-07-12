#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(vlt => 1);

run(cmd => ["$ENV{VERILATOR_ROOT}/bin/verilator",
            "--output-concatenation-groups", "10",
            "--debug-test-concatenation",
            "$Self->{t_dir}/t_output_concatenation_groups_splitting.dat"],
    logfile => "$Self->{obj_dir}/output_concatenation_groups.log",
    expect_filename => $Self->{golden_filename},
    tee => 0,
    verilator_run => 1,
    fails => 0,
    );

ok(1);
1;
