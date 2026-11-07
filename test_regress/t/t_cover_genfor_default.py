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

cov_flags = ['--binary', '--coverage-line', '--coverage-branch', '--coverage-expr']


def run_and_check(golden):
    test.execute(all_run_flags=[" +verilator+coverage+file+" + test.obj_dir + "/coverage.dat"])
    test.files_identical(test.obj_dir + "/coverage.dat", golden)


# Default (no --coverage-per-instance): the hierarchy stays the enclosing
# module, so generate-for iterations still merge and the report matches the
# pre-change behavior -- proving the fix does not alter default reports.
test.compile(top_filename="t/t_cover_genfor.v", verilator_flags2=cov_flags)
run_and_check("t/t_cover_genfor_default.dat.out")

test.passes()
