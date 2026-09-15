#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('simulator')

if not test.have_solver:
    test.skip("No constraint solver installed")

test.compile()

# THIS TEST FAILS ON MASTER, BY DESIGN. Constraints denoting the same solution
# set randomize differently depending on how they are spelled, and arms of equal
# measure are not equiprobable.
# See the header of t_constraint_rand_cond_equiv.v.
test.execute(all_run_flags=["+verilator+seed+1"])

test.passes()
