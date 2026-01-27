#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2025 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('simulator')

test.compile(verilator_flags2=['--binary', '--stats', '-fno-inline', '--unroll-count', '0'])

test.file_grep(test.stats, r'NBA, variables using ShadowVar scheme\s+(\d+)', 2)
test.file_grep(test.stats, r'NBA, variables using ShadowVarMasked scheme\s+(\d+)', 2)
test.file_grep(test.stats, r'NBA, variables using FlagShared scheme\s+(\d+)', 2)
test.file_grep(test.stats, r'NBA, variables using FlagUnique scheme\s+(\d+)', 2)
test.file_grep(test.stats, r'NBA, variables using ValueQueuePartial scheme\s+(\d+)', 2)

test.execute()

test.passes()
