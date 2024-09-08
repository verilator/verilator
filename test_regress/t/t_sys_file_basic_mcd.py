#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('simulator')

test.unlink_ok(test.obj_dir + "/t_sys_file_basic_mcd.log")

test.compile()

test.execute(expect_filename=test.golden_filename)

test.files_identical(test.obj_dir + "/t_sys_file_basic_mcd_test2_0.dat",
                     test.t_dir + "/t_sys_file_basic_mcd_test2_0.dat")
test.files_identical(test.obj_dir + "/t_sys_file_basic_mcd_test2_1.dat",
                     test.t_dir + "/t_sys_file_basic_mcd_test2_1.dat")
test.files_identical(test.obj_dir + "/t_sys_file_basic_mcd_test2_2.dat",
                     test.t_dir + "/t_sys_file_basic_mcd_test2_2.dat")
test.files_identical(test.obj_dir + "/t_sys_file_basic_mcd_test5.dat",
                     test.t_dir + "/t_sys_file_basic_mcd_test5.dat")

test.passes()
