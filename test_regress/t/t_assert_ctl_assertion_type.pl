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

compile(
    make_top_shell => 0,
    make_main => 0,
    verilator_flags2 => ["--assert", "--timing", "--coverage-user", "--exe $Self->{t_dir}/$Self->{name}.cpp"],
    nc_flags2 => ["+nccovoverwrite", "+nccoverage+all", "+nccovtest+$Self->{name}"],
    );

execute(
    all_run_flags => ["+verilator+error+limit+100"],
    expect_filename => $Self->{golden_filename},
    );

files_identical($Self->{coverage_filename}, "t/t_assert_ctl_assertion_type_coverage.out");

ok(1);
1;
