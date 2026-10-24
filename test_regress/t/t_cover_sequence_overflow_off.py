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
test.top_filename = 't/t_cover_sequence_overflow.v'

test.compile(verilator_flags2=['--assert', '--binary', '--stats'])

test.execute()
test.file_grep_not(test.run_log_filename, r'Cover sequence match count overflowed')
test.file_grep(test.stats, r'Assertions, cover statements\s+(\d+)', 1)

test.passes()
