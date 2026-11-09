#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2024 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vltmt')
test.top_filename = "t/t_threads_counter.v"

test.compile(verilator_flags2=['--cc', '--stats', '-CFLAGS -DVL_THREADS_SERIAL_COST=0'], threads=2)

test.execute()

# Threads synchronize through progress words
test.file_grep(test.stats, r'Optimizations, Thread progress waits\s+[1-9]')

test.passes()
