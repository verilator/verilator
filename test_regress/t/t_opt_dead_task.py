#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2025 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('simulator')

test.compile(verilator_flags2=["--stats", "--top-module t"])

if test.vlt_all:
    test.file_grep(test.stats, r'Optimizations, deadified FTasks\s+(\d+)', 6)

test.execute()

test.file_grep(test.run_log_filename, r'static-still-live')
test.file_grep_not(test.run_log_filename, r'static-made-in-dead')

test.passes()
