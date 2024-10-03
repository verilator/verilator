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
test.top_filename = "t/t_unroll_pragma.v"

test.compile(verilator_flags2=['--unroll-count 4 --unroll-stmts 9999 --stats -DTEST_FULL'],
             verilator_make_gmake=False,
             make_top_shell=False,
             make_main=False)

test.file_grep(test.stats, r'Optimizations, Unrolled Loops\s+(\d+)', 5)

test.passes()
