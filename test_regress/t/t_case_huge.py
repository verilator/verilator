#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('simulator')

test.compile(verilator_flags2=["--stats"])

if test.vlt:
    test.file_grep(test.stats, r'Optimizations, Tables created\s+(\d+)', 10)
    test.file_grep(test.stats, r'Optimizations, Combined CFuncs\s+(\d+)', 8)
elif test.vltmt:
    test.file_grep(test.stats, r'Optimizations, Tables created\s+(\d+)', 10)
    test.file_grep(test.stats, r'Optimizations, Combined CFuncs\s+(\d+)', 9)

test.execute()

test.passes()
