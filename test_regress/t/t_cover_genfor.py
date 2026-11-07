#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3,
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('simulator')

cov_flags = ['--binary',
             '--coverage-line',
             '--coverage-branch',
             '--coverage-expr',
             '--coverage-per-instance']


def run_and_check(golden):
    test.execute(all_run_flags=[" +verilator+coverage+file+" + test.obj_dir + "/coverage.dat"])
    test.files_identical(test.obj_dir + "/coverage.dat", golden)


# --coverage-per-instance: each unrolled generate-for iteration reports
# separately, with a distinct hierarchy per iteration (labeled g_loop,
# unlabeled genblk2, and nested g_nest).
test.compile(verilator_flags2=cov_flags)
run_and_check("t/t_cover_genfor.dat.out")

test.passes()
