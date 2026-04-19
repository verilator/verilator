#!/usr/bin/env python3
# DESCRIPTION: Verilator: FSM coverage same-state multi-case test
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('simulator')

# This test keeps two candidate case statements on the same state variable in a
# single always_ff. That specifically targets the "same varscope, process both"
# branch in processAlways(), as opposed to the existing FSMMULTI warning test
# that covers the different-varscope warning path.
test.compile(verilator_flags2=['--cc --coverage-fsm'])

test.execute()

# The key assertion here is that the second same-var candidate still contributes
# coverage points. In this small runtime we reliably observe the destination
# state point, even though the exact arc count depends on the ordering of the
# two case statements sharing the same current-state value.
test.file_grep(test.obj_dir + "/coverage.dat", r"S0->S1")
test.file_grep(test.obj_dir + "/coverage.dat", r"t.state::S2")
test.file_grep_not(test.obj_dir + "/vlt_compile.log", r"FSMMULTI")

test.passes()
