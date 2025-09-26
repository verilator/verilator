#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('simulator')

test.compile(
    verilator_flags2=["-unroll-count 1024", test.wno_unopthreads_for_few_cores, "--stats"])

test.execute(expect_filename=test.golden_filename)

if test.vlt:
    # Note, with vltmt this might be split differently, so only checking vlt
    test.file_grep(test.stats, r'Optimizations, Reloop iterations\s+(\d+)', 125)
    test.file_grep(test.stats, r'Optimizations, Reloops\s+(\d+)', 2)

test.passes()
