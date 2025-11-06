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

test.top_filename = "t/t_opt_balance_cats.v"

test.compile(verilator_flags2=[
    "--stats", "--build", "--gate-stmts", "10000", "--expand-limit", "128", "--sc"
])

test.file_grep(test.stats, r'Optimizations, FuncOpt concat trees balanced\s+(\d+)', 1)
test.file_grep(test.stats, r'Optimizations, FuncOpt concat splits\s+(\d+)', 0)

test.passes()
