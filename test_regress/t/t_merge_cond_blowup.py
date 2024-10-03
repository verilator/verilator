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

# TODO: This takes excessively long on vltmt, this should be fixed

test.compile(verilator_flags2=["--unroll-count 1000000000", "--output-split 0", "--stats"])

test.execute()

if test.vlt:
    # Note, with vltmt this might be split differently, so only checking vlt
    test.file_grep(test.stats, r'Optimizations, MergeCond merges\s+(\d+)', 500)
    # V3MergeCond.cpp MAX_DISTANCE
    test.file_grep(test.stats, r'Optimizations, MergeCond merged items\s+(\d+)', 1000)
    # V3MergeCond.cpp MAX_DISTANCE *2
    test.file_grep(test.stats, r'Optimizations, MergeCond longest merge\s+(\d+)', 2)

test.passes()
