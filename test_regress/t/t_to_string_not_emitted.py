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

test.top_filename = "t_to_string_emitted.v"

test.compile(verilator_flags2=["--stats"])

test.execute()

test.file_grep(test.stats, r"Optimizations, Struct/union ToString emitted\s+(\d+)", 0)
test.file_grep(test.stats, r"Optimizations, Class ToString emitted\s+(\d+)", 0)
test.file_grep(test.stats, r"Optimizations, Interface ToString emitted\s+(\d+)", 0)

test.passes()
