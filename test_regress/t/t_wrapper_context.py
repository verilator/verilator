#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Multiple Model Test Module
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt_all')

test.compile(
    make_top_shell=False,
    make_main=False,
    # link threads library, add custom .cpp code, add tracing & coverage support
    verilator_flags2=["--exe", test.pli_filename, "--trace-vcd --coverage -cc"],
    threads=1,
    make_flags=['CPPFLAGS_ADD=-DVL_NO_LEGACY'])

test.execute()
test.files_identical_sorted(test.obj_dir + "/coverage_top0.dat",
                            "t/t_wrapper_context__top0.dat.out")
test.files_identical_sorted(test.obj_dir + "/coverage_top1.dat",
                            "t/t_wrapper_context__top1.dat.out")

test.vcd_identical(test.obj_dir + "/trace0.vcd", "t/t_wrapper_context__trace0.vcd.out")
test.vcd_identical(test.obj_dir + "/trace1.vcd", "t/t_wrapper_context__trace1.vcd.out")

test.passes()
