#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.priority(30)
test.scenarios('vlt')
test.top_filename = "t/t_hier_block.v"

# Compilation of hierarchical blocks is skipped if their libs exist
test.clean_objs()

test.compile(v_flags2=['t/t_hier_block.cpp'],
             verilator_flags2=['-fno-inline', '--hierarchical', '--Wno-TIMESCALEMOD'])

test.execute()

test.passes()
