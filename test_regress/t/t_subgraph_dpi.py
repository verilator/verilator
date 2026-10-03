#!/usr/bin/env python3
# DESCRIPTION: Verilator: DPI-C import participates in a subgraph
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt')
test.pli_filename = "t/t_subgraph_dpi_c.cpp"
test.compile(v_flags2=[test.pli_filename],
             verilator_flags2=["--binary", "--subgraph-schedule", "--stats"])
test.execute()
test.file_grep(test.stats, r'Scheduling, Subgraph early groups\s+(\d+)', 2)
test.file_grep(test.stats, r'Scheduling, Subgraph early fallbacks\s+(\d+)', 0)
test.passes()
