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

# Very hard to reliably trigger run-time race on small design,
# use ThreadSanitizer to test
test.enable_tsan()

test.compile(verilator_flags2=['--binary', '-fno-dfg', '--no-threads-coarsen'], threads=2)

test.execute(fails='any')  # Now failing, fix pending

test.passes()
