#!/usr/bin/env python3
# DESCRIPTION: Verilator: FSM coverage negative extraction test
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('simulator')

# This test is intentionally "half supported": one case item is a simple
# direct state assignment, while the others use shapes the extractor should
# ignore (multiple meaningful statements or assignment to a non-state lhs).
# That lets us hit the conservative negative branches in directStateAssign()
# and singleMeaningfulStmt() without changing user-visible behavior.
test.compile(verilator_flags2=['--cc --coverage-fsm'])

test.execute()

test.file_grep(test.obj_dir + "/coverage.dat", r"fsm_state")
test.file_grep(test.obj_dir + "/coverage.dat", r"S0->S1")
test.file_grep_not(test.obj_dir + "/coverage.dat", r"S1->S2")
test.file_grep_not(test.obj_dir + "/coverage.dat", r"S2->S0")

test.passes()
