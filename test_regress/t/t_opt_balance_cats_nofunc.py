#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2024 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt')

test.top_filename = "t/t_opt_balance_cats.v"

test.compile(verilator_flags2=[
    "--stats", "-fno-func-opt", "-fno-func-opt-balance-cat", "-fno-func-opt-split-cat"
])

test.file_grep_not(test.stats, r'Optimizations, FuncOpt concat trees balances')
test.file_grep_not(test.stats, r'Optimizations, FuncOpt concat splits')

test.passes()
