#!/usr/bin/env python3
# DESCRIPTION: Verilator: Subgraph fallback warning locates a combinational cycle
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt')
test.lint(verilator_flags2=["--subgraph-schedule", "-Wno-fatal", "-Wno-UNOPTFLAT"],
          expect_filename="t/t_subgraph_fallback_cycle_line.out")
test.passes()
