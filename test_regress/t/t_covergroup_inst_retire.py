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

# Deliberately compiled WITHOUT --coverage, which is what unlocks the free path
# in VlCovergroupType::retire().  Under --coverage the node is retained instead;
# t_covergroup_inst_lifetime pins that side.
test.compile()

test.execute()

test.passes()
