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

# Use very low thresholds to test "too large to inline" code path
# --inline-cfuncs 1: only inline functions with <= 1 node (essentially nothing)
# --inline-cfuncs-product 1: product threshold also very low
test.compile(verilator_flags2=[
    "--stats", "--exe", "--main", "--inline-cfuncs", "1", "--inline-cfuncs-product", "1"
])

# With such low thresholds, very few or no functions should be inlined
# This exercises the "return false" path in isInlineable()
test.file_grep(test.stats, r'Optimizations, Inlined CFuncs\s+(\d+)')

test.execute()

test.passes()
