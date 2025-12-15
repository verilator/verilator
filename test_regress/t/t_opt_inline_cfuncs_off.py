#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt')
test.top_filename = "t/t_opt_inline_cfuncs.v"

# Disable inlining with --inline-cfuncs 0
test.compile(verilator_flags2=["--stats", "--binary", "--inline-cfuncs", "0"])

# Verify inlining did NOT happen (stat doesn't exist when pass is skipped)
test.file_grep_not(test.stats, r'Optimizations, Inlined CFuncs\s+[1-9]')

test.execute()

test.passes()
