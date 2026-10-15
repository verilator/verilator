#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vltmt')
test.top_filename = "t/t_gen_alw.v"  # Self-checking, multiple always blocks

# Threads synchronize with per-thread progress words. Run every evaluation on the thread pool,
# also with execution profiling, which records waits on progress words.
test.compile(v_flags2=["--prof-exec", "--stats", "-CFLAGS -DVL_THREADS_SERIAL_COST=0"], threads=4)

test.execute(
    all_run_flags=["+verilator+prof+exec+start+0", " +verilator+prof+exec+file+/dev/null"])

test.file_grep(test.stats, r'Optimizations, Thread progress publishes\s+[1-9]')
test.file_grep(test.stats, r'Optimizations, Thread progress waits\s+[1-9]')

test.passes()
