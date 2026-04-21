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

test.compile(verilator_flags2=['--binary --trace-vcd --timing'])

test.execute()

# Two class-driven clocks toggle in lockstep: 10 highs and 10 lows total.
test.file_grep_count(test.trace_filename, r'(?m)^1[!-~]$', 10)
test.file_grep_count(test.trace_filename, r'(?m)^0[!-~]$', 10)

test.passes()
