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

test.compile(top_filename="t/t_cover_genfor.v",
             verilator_flags2=[
                 '--binary',
                 '--coverage-line',
                 '--coverage-branch',
                 '--coverage-expr',
                 '--coverage-per-instance',
                 '--top-module',
                 'tb',
             ])

test.execute(all_run_flags=[" +verilator+coverage+file+" + test.obj_dir + "/coverage.dat"])

cov = test.obj_dir + "/coverage.dat"

test.files_identical(cov, "t/t_cover_genfor.dat.out")

test.passes()
