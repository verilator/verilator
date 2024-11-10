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

test.top_filename = "t/t_dfg_balance_cats.v"

test.compile(verilator_flags2=["--stats", "-fno-func-opt"])

test.file_grep(test.stats,
               r' Optimizations, DFG pre inline BalanceTrees, concat trees balanced\s+(\d+)', 0)
test.file_grep(test.stats,
               r' Optimizations, DFG post inline BalanceTrees, concat trees balanced\s+(\d+)', 1)
test.file_grep(test.stats, r'Optimizations, DFG pre inline Dfg2Ast, result equations\s+(\d+)', 1)
test.file_grep(test.stats, r'Optimizations, DFG post inline Dfg2Ast, result equations\s+(\d+)', 1)
test.file_grep_not(test.stats, r'Optimizations, FuncOpt concat splits')

test.passes()
