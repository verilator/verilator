#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('simulator')

# --output-split-cfuncs forces the process to be split into sub-functions
test.compile(verilator_flags2=["--binary", "--output-split-cfuncs", "20"])

# Confirm the split actually happened: the 'initial' timing process is emitted
# as function sub-parts (__Vtiming__0__0 / __Vtiming__0__1). Without the split
# this test would not exercise the bug it guards against -- a dynamic 'wait
# fork' trigger temporary separated from its uses across a sub-function boundary.
if test.vlt_all:
    test.file_grep(test.obj_dir + "/V" + test.name + "_t__0.cpp", r'__Vtiming__0__1\b')

test.execute()

test.passes()
