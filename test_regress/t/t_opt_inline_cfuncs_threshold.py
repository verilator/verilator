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

# Use thresholds that guarantee rejection to test the "return false" path in isInlineable()
# --inline-cfuncs 1: pass still runs (not skipped)
# --inline-cfuncs-product 0: guarantees all functions rejected (node_count * call_count > 0 always)
test.compile(verilator_flags2=[
    "--stats", "--binary", "--inline-cfuncs", "1", "--inline-cfuncs-product", "0"
])

test.file_grep(test.stats, r'Optimizations, Inlined CFuncs\s+(\d+)', 0)

test.execute()

test.passes()
