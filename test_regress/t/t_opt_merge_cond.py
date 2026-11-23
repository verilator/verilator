#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2024 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt_all')

test.compile(verilator_flags2=["-unroll-count 64", "--stats", "-fno-decompose"])

test.execute()

if test.vlt:
    # Note, with vltmt this might be split differently, so only checking vlt
    test.file_grep(test.stats, r'Optimizations, MergeCond merges\s+(\d+)',
                   11 if test.repcut else 12)
    test.file_grep(test.stats, r'Optimizations, MergeCond merged items\s+(\d+)',
                   521 if test.repcut else 590)
    test.file_grep(test.stats, r'Optimizations, MergeCond longest merge\s+(\d+)',
                   65 if test.repcut else 129)

test.passes()
