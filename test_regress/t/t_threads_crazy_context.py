#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt_all')
test.top_filename = "t/t_threads_crazy.v"

test.compile(verilator_flags2=['--cc'], threads=(2 if test.vltmt else 1), context_threads=1024)

test.execute()

if test.vltmt:
    test.file_grep(
        test.run_log_filename,
        r'System has \d+ hardware threads but simulation thread count set to 1024\. This will likely cause significant slowdown\.'
    )

test.passes()
