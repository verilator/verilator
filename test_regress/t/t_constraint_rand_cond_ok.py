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

# This one PASSES on master. It pins the behaviour in this area that is already
# correct, in particular that a guarded arm holding one solution of 2**24 stays
# rare, so that a fix for the companion tests cannot "fix" them by making every
# rand condition a 50/50 coin - which IEEE 1800-2023 18.5.10 rules out.
test.execute(all_run_flags=["+verilator+seed+1"])

test.passes()
