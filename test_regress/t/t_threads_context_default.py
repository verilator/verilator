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
test.top_filename = "t/t_threads_crazy.v"
test.pli_filename = "t/t_threads_context_default.cpp"

# Model uses more threads than the host has, and the testbench does not set
# the context thread count, so the thread count must grow to fit the model
test.compile(make_main=False, verilator_flags2=['--cc', '--exe', test.pli_filename], threads=1024)

test.execute()

test.file_grep(
    test.run_log_filename,
    r'Process has \d+ hardware threads available, but simulation thread count set to 1024\. This will likely cause significant slowdown\.'
)

test.passes()
