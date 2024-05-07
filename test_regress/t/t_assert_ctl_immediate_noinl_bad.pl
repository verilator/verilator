#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

top_filename("t_assert_ctl_immediate_bad.v");
golden_filename("t/t_assert_ctl_immediate_bad.out");
scenarios(vlt => 1);

compile(
    verilator_flags2 => ['--assert --timing --fno-inline'],
    );

execute(
    all_run_flags => ["+verilator+error+limit+100"],
    expect_filename => $Self->{golden_filename},
    );

ok(1);
1;
