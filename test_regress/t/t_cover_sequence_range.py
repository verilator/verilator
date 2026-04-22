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
test.fourstate_capable = False

test.sim_time = 2500
test.compile(timing_loop=True,
             verilator_flags2=['--assert', '--coverage-user', '--timing', '--stats'])
test.execute()

if test.vlt_all:
    test.file_grep(test.stats, r'Assertions, NFA delay ring edge visits\s+(\d+)', 19)
    test.inline_checks()

test.passes()
