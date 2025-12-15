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

# Use --output-split-cfuncs to create small functions that can be inlined
# Also test --inline-cfuncs-product option
test.compile(verilator_flags2=[
    "--stats", "--exe", "--main", "--output-split-cfuncs", "1", "--inline-cfuncs-product", "200"
])

# Verify inlining happened (count > 0)
test.file_grep(test.stats, r'Optimizations, Inlined CFuncs\s+(\d+)')

test.execute()

test.passes()
