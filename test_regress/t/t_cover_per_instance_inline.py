#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3,
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import os

import vltest_bootstrap

test.scenarios('simulator')
test.fourstate_capable = False

test.compile(top_filename="t/t_cover_per_instance.v",
             v_flags2=["+define+INLINE_CHILD"],
             verilator_flags2=[
                 '--binary',
                 '--coverage-line',
                 '--coverage-per-instance',
                 '--top-module',
                 'tb',
                 '--timing',
             ])

test.execute(all_run_flags=[" +verilator+coverage+file+" + test.obj_dir + "/coverage.dat"])

cov = test.obj_dir + "/coverage.dat"

test.files_identical(cov, "t/t_cover_per_instance.dat.out")

test.run(cmd=[
    os.environ["VERILATOR_ROOT"] + "/bin/verilator_coverage",
    "--annotate-points",
    "--annotate",
    test.obj_dir + "/annotated-points",
    cov,
],
         verilator_run=True)

test.files_identical(test.obj_dir + "/annotated-points/t_cover_per_instance.v",
                     "t/t_cover_per_instance.out")

test.passes()
