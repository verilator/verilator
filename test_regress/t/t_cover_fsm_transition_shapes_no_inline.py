#!/usr/bin/env python3
# DESCRIPTION: Verilator: FSM coverage hierarchy with module inlining disabled
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

# Same as t_cover_fsm_transition_shapes_multi, but without module inlining,
# which must not change the coverage output.

import vltest_bootstrap

test.scenarios('simulator')
test.top_filename = "t/t_cover_fsm_transition_shapes_multi.v"

test.compile(verilator_flags2=['--cc --coverage-fsm', '-fno-inline'])

test.execute()

test.files_identical(test.obj_dir + "/coverage.dat", "t/t_cover_fsm_transition_shapes_multi.out")

test.passes()
