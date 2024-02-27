#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003-2009 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(simulator => 1);

compile(
    verilator_flags2 => ['--cc --coverage-toggle --stats'],
    );

execute(
    check_finished => 1,
    );

# Read the input .v file and do any CHECK_COVER requests
inline_checks();

file_grep_not("$Self->{obj_dir}/coverage.dat", "largeish");

file_grep($Self->{stats}, qr/Coverage, Toggle points joined\s+(\d+)/i, 23)
    if $Self->{vlt_all};

run(cmd => ["$ENV{VERILATOR_ROOT}/bin/verilator_coverage",
            "--annotate", "$Self->{obj_dir}/annotated",
            "$Self->{obj_dir}/coverage.dat",
            ],
    verilator_run => 1,
    );

files_identical("$Self->{obj_dir}/annotated/$Self->{name}.v", $Self->{golden_filename});

run(cmd => ["$ENV{VERILATOR_ROOT}/bin/verilator_coverage",
            "--annotate-points",
            "--annotate", "$Self->{obj_dir}/annotated-points",
            "$Self->{obj_dir}/coverage.dat",
            ],
    verilator_run => 1,
    );

files_identical("$Self->{obj_dir}/annotated-points/$Self->{name}.v", "t/" . $Self->{name} . "_points.out");

ok(1);
1;
