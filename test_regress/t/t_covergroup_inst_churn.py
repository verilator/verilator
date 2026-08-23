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

# CHURN + 3 clock edges at 10 time units each.  The default 1100 gives ~110 edges,
# far short of the churn the sentinel needs to be convincing.
test.sim_time = 25000

# Deliberately WITHOUT --coverage: under --coverage the coverage database holds
# raw pointers into each instance's counts and nodes must be retained instead
# (see t_covergroup_inst_lifetime).  Freeing is unlocked only without coverage.
test.compile()

test.execute()

test.passes()
