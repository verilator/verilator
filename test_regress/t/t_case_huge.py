#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2024 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('simulator')

# This tests combining CFuncs, but Dfg would inline the submodule, disabling
test.compile(verilator_flags2=["--stats", "-fno-dfg"])

test.execute()

test.file_grep(test.stats, r'Optimizations, Cases table normal\s+(\d+)', 8)
test.file_grep(test.stats, r'Optimizations, Cases table tiny\s+(\d+)', 0)
test.file_grep(test.stats, r'Optimizations, Cases parallelized\s+(\d+)', 3)
test.file_grep(test.stats, r'Optimizations, Tables created\s+(\d+)', 2)
test.file_grep(test.stats, r'Optimizations, Combined CFuncs\s+(\d+)', 9 if test.vltmt else 8)

test.passes()
