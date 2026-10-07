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
test.top_filename = "t/t_threads_serial_fallback.v"

# The falling-edge logic costs less than this, but testing all trigger conditions costs more,
# so no pass is nearly empty
test.compile(verilator_flags2=["--stats", "--threads-serial-cost", "30"], threads=2)

test.file_grep_not(test.stats, r'Optimizations, Thread serial fallbacks')

test.execute()

test.passes()
