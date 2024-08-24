#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(simulator => 1);

compile(
    verilator_flags2 => ['--binary', '--coverage-toggle'],
    );

execute(
    all_run_flags => [" +verilator+coverage+file+$Self->{obj_dir}/coverage.dat"],
    );

if (-e ("$Self->{obj_dir}/coverage.dat")) {  # Don't try to write .info if test was skipped
    run(cmd => ["$ENV{VERILATOR_ROOT}/bin/verilator_coverage",
            "-write-info", "$Self->{obj_dir}/coverage.info",
            "$Self->{obj_dir}/coverage.dat",
            ],
    verilator_run => 1,
    );

    files_identical("$Self->{obj_dir}/coverage.info", $Self->{name} . ".info.out");
}

ok(1);
1;
