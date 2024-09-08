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

test.lint()

for filename in glob.glob(test.obj_dir + "/*"):
    if (re.search(r'\.log', filename)  # Made by driver.py, not Verilator sources
            or re.search(r'\.status', filename)  # Made by driver.py, not Verilator sources
            or re.search(r'\.gcda', filename)):  # Made by gcov, not Verilator sources
        continue
    test.error("%Error: Created '" + filename + "', but --lint-only shouldn't create files")

test.passes()
