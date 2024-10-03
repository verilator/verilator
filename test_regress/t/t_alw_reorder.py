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

test.compile(verilator_flags2=["--stats"])

test.file_grep(test.stats, r'Optimizations, Split always\s+(\d+)', 0)

# Important: if reorder succeeded, we should see no dly vars.
# Equally important: twin test t_alw_noreorder should see dly vars,
#  is identical to this test except for disabling the reorder step.
for filename in (test.glob_some(test.obj_dir + "/" + test.vm_prefix + "*.h") +
                 test.glob_some(test.obj_dir + "/" + test.vm_prefix + "*.cpp")):
    test.file_grep_not(filename, r'dly__t__DOT__v1')
    test.file_grep_not(filename, r'dly__t__DOT__v2')
    test.file_grep_not(filename, r'dly__t__DOT__v3')

test.execute()

test.passes()
