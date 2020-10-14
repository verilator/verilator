#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003-2009 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(dist => 1);

run(cmd => ["../bin/verilator_coverage",
            "--no-unlink", "--nounlink",
            "--write", "$Self->{obj_dir}/coverage.dat",
            "t/t_vlcov_data_a.dat",
            "t/t_vlcov_data_b.dat",
            "t/t_vlcov_data_c.dat",
            "t/t_vlcov_data_d.dat",
    ],
    verilator_run => 1,
    );

# Not deleted e.g. parsed --no-unlink properly
files_identical("$Self->{t_dir}/t_vlcov_data_a.dat",
                "$Self->{t_dir}/t_vlcov_data_a.dat");

# Older clib's didn't properly sort maps, but the coverage data doesn't
# really care about ordering. So avoid false failures by sorting.
files_identical_sorted("$Self->{obj_dir}/coverage.dat", $Self->{golden_filename});

ok(1);
1;
