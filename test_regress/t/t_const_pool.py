#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt')

test.compile(verilator_flags2=["--binary", "--stats"])

test.execute()

test.file_grep(test.stats, r'ConstPool, CONST emitted\s+(\d+)', 2)
test.file_grep(test.stats, r'ConstPool, CONSARRAY emitted\s+(\d+)', 3)
test.file_grep(test.stats, r'ConstPool, CONSASSOC emitted\s+(\d+)', 3)
test.file_grep(test.stats, r'ConstPool, CONSDYNARRAY emitted\s+(\d+)', 1)
test.file_grep(test.stats, r'ConstPool, CONSQUEUE emitted\s+(\d+)', 4)
test.file_grep(test.stats, r'ConstPool, CONSSTRUCT emitted\s+(\d+)', 5)
test.file_grep(test.stats, r'ConstPool, CONSWILDCARD emitted\s+(\d+)', 1)

test.passes()
