#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt_all')
test.top_filename = "t/t_alw_reorder.v"
test.compile(verilator_flags2=["--stats -fno-reorder"])

test.file_grep(test.stats, r'Optimizations, Split always\s+(\d+)', 0)
# Here we should see some dly vars since reorder is disabled.
# (Whereas our twin test, t_alw_reorder, should see no dly vars
#  since it enables the reorder step.)
files = test.glob_some(test.obj_dir + "/" + test.vm_prefix + "___024root*.cpp")
test.file_grep_any(files, r'dly__t__DOT__v1')
test.file_grep_any(files, r'dly__t__DOT__v2')

test.execute()

test.passes()
