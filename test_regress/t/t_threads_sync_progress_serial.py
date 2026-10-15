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

# With the default cost limit, cheap evaluations run on the calling thread without the
# progress words, and the rest on the thread pool with them; both must stay in step.
test.compile(v_flags2=["--stats"], threads=4)

test.execute()

test.file_grep(test.stats, r'Optimizations, Thread progress waits\s+[1-9]')

test.passes()
