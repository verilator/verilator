#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 by Marco Bartoli.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt')

test.compile(verilator_flags2=['--binary --trace-vcd'])

test.execute()

test.file_grep(test.trace_filename, r'^\$enddefinitions \$end')
test.file_grep_not(test.trace_filename, r'^\s*\$var\s')

test.passes()
