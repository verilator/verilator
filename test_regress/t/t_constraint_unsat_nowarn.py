#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2026 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('simulator')
test.top_filename = "t/t_constraint_unsat.v"

if not test.have_solver:
    test.skip("No constraint solver installed")

test.compile()

# Test with warnings disabled via +verilator+wno+unsatconstr+1
test.execute(all_run_flags=['+verilator+wno+unsatconstr+1'],
             expect_filename=test.golden_filename)

test.passes()
