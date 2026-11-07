#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios("simulator")
test.enable_tsan()
test.top_filename = "t/t_timing_dpi_func_nested_bad.v"
test.pli_filename = "t/t_timing_dpi_func_nested_bad.cpp"
test.golden_filename = "t/t_timing_dpi_func_nested_bad.out"

# Compile each file separately, so DPI calls and exports are in different translation units
test.compile(
    v_flags2=[test.pli_filename],
    verilator_flags2=["--binary", "--stats", "-MAKEFLAGS", "VM_PARALLEL_BUILDS=1"],
)

if test.vlt_all:
    test.file_grep(test.stats, r'Timing, suspendable DPI exports\s+(\d+)', 1)

test.execute(fails=True, expect_filename=test.golden_filename)

test.passes()
