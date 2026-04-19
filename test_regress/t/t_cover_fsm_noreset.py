#!/usr/bin/env python3
# DESCRIPTION: Verilator: FSM coverage no-reset lowering test
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('simulator')

# This test deliberately uses a clocked FSM with no outer reset branch. It
# keeps coverage extraction in the supported subset, but forces lowering down
# the "hasResetCond() == false" path so we validate the no-reset machinery
# rather than only reset-wrapped FSMs.
test.compile(verilator_flags2=['--cc --coverage-fsm'])

test.execute()

test.file_grep(test.obj_dir + "/coverage.dat", r"fsm_state")
test.file_grep(test.obj_dir + "/coverage.dat", r"fsm_arc")
test.file_grep(test.obj_dir + "/coverage.dat", r"S0->S1")
test.file_grep_not(test.obj_dir + "/coverage.dat", r"ANY->")

test.passes()
