#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap
import sys

if sys.platform != "linux":
    test.skip("This test uses /proc/self/task to count number of active threads.")

test.scenarios("vlt")
test.top_filename = "t/t_timing_dpi_thread_leak.v"

test.compile(
    v_flags2=["t/t_timing_dpi_thread_leak.cpp"],
    verilator_flags2=["--binary", "--stats"],
)

if test.vlt_all:
    test.file_grep(test.stats, r'Timing, suspendable DPI exports\s+(\d+)', 1)

test.execute()

test.passes()
