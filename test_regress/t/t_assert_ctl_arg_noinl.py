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
test.top_filename = "t_assert_ctl_arg.v"

test.compile(make_top_shell=False,
             make_main=False,
             verilator_flags2=[
                 "--assert", "--timing", "--coverage-user", "--exe",
                 test.t_dir + "/t_assert_ctl_arg.cpp", "-fno-inline"
             ],
             nc_flags2=["+nccovoverwrite", "+nccoverage+all", "+nccovtest+" + test.name])

test.execute(all_run_flags=["+verilator+error+limit+100"],
             expect_filename=test.t_dir + "/t_assert_ctl_arg.out")

test.files_identical(test.coverage_filename, test.t_dir + "/t_assert_ctl_arg.coverage.out")

test.passes()
