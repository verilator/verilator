#!/usr/bin/env python3
# DESCRIPTION: Verilator: FSM coverage ignores a register written as a concatenation
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('simulator')

# -fno-const-before-dfg keeps the concatenation on the left of the assignment
test.compile(verilator_flags2=['--cc --coverage-fsm -fno-const-before-dfg'])

test.execute()

test.file_grep_not(test.obj_dir + "/coverage.dat", r"fsm_")

test.passes()
