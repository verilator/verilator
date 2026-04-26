#!/usr/bin/env python3
# DESCRIPTION: Verilator: FSM coverage ignores forced non-enum state variables that are too wide
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('simulator')

test.compile(verilator_flags2=['--cc --coverage-fsm'])

test.execute()

test.files_identical(test.obj_dir + "/coverage.dat", "t/" + test.name + ".out")

test.passes()
