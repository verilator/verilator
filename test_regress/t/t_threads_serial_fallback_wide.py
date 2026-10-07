#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt_all')
test.sim_time = 3000

# A cost the derived clock passes stay under, including testing all trigger conditions, but
# the main clock passes exceed
test.compile(verilator_flags2=["--stats", "--threads-serial-cost", "8000"],
             threads=(2 if test.vltmt else 1))

if test.vltmt:
    test.file_grep(test.stats, r'Optimizations, Thread serial fallbacks\s+(\d+)', 1)
else:
    test.file_grep_not(test.stats, r'Optimizations, Thread serial fallbacks')

test.execute()

test.passes()
