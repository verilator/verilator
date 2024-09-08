#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt')

test.compile(
    make_top_shell=False,
    make_main=False,
    verilator_flags2=["--assert", "--timing", "--coverage-user", "--exe", test.pli_filename],
    nc_flags2=["+nccovoverwrite", "+nccoverage+all", "+nccovtest+" + test.name])

test.execute(all_run_flags=["+verilator+error+limit+100"], expect_filename=test.golden_filename)

test.files_identical(test.coverage_filename, test.t_dir + "/t_assert_ctl_arg_coverage.out")

test.passes()
