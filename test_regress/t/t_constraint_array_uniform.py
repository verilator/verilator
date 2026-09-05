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

# THIS TEST FAILS ON MASTER, BY DESIGN. A rand array solved through the
# constraint solver takes grossly non-uniform values even under a constraint
# that excludes nothing. See the header of t_constraint_array_uniform.v.
#
# Fixed seed so the bands are deterministic run to run.
test.execute(all_run_flags=["+verilator+seed+1"])

test.passes()
