#!/usr/bin/env python3
# DESCRIPTION: Verilator: SystemVerilog test for calling a task from function context through DPI
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2024 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios("simulator")
test.top_filename = "t/t_timing_dpi_func_bad.v"

test.compile(
    v_flags2=["t/t_timing_dpi_func_bad.cpp"],
    verilator_flags2=["--binary", "--trace-fst"],
)

if test.vlt_all:
    test.execute(fails=True, expect_filename=test.golden_filename)

test.passes()
