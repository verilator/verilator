#!/usr/bin/env python3
# DESCRIPTION: Verilator: Fallback of a subgraph with independent clocks preserves both events
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt')
test.compile(verilator_flags2=["--binary", "--subgraph-schedule", "--stats", "-Wno-fatal"])
test.execute()

test.file_grep(test.stats, r'Scheduling, Subgraph early candidates\s+(\d+)', 1)
test.file_grep(test.stats, r'Scheduling, Subgraph early fallbacks\s+(\d+)', 1)

test.passes()
