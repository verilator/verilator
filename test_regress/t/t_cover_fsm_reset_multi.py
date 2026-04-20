#!/usr/bin/env python3
# DESCRIPTION: Verilator: FSM coverage reset pseudo-vertex reuse test
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('simulator')

# This regression is aimed at the graph helper, not at recommending RTL style.
# We deliberately create two reset arcs in a single FSM so graph construction
# has to reuse the synthetic ANY reset pseudo-vertex rather than allocating it
# only once for a one-arc machine.
test.compile(verilator_flags2=['--cc --coverage-fsm'])

test.execute()

test.file_grep(test.obj_dir + "/coverage.dat", r"ANY->S0\[reset_include\]")
test.file_grep(test.obj_dir + "/coverage.dat", r"ANY->S1\[reset_include\]")
test.file_grep(test.obj_dir + "/coverage.dat", r"fsm_arc")

test.passes()
