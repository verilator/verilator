#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Leela Pakanati
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('simulator')
test.top_filename = "t/t_interface_nested_port.v"

# Run with -fno-inline to explicitly test no-inline mode.
# The same test file works with both inline and no-inline modes.
test.compile(verilator_flags2=['--binary', '-fno-inline'])
test.execute()
test.passes()
