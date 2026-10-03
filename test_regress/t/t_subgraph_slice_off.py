#!/usr/bin/env python3
# DESCRIPTION: Verilator: Sliced state preserves scheduling across hierarchical boundaries
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt')
test.top_filename = 't/t_subgraph_slice.v'
test.sim_time = 7000
test.compile(verilator_flags2=[])
test.execute(expect_filename='t/t_subgraph_slice.out')
test.passes()
