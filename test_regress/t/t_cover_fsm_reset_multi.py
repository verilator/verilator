#!/usr/bin/env python3
# DESCRIPTION: Verilator: FSM coverage reset pseudo-vertex reuse test
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import os

import vltest_bootstrap

test.scenarios('simulator')

# This regression is aimed at the graph helper, not at recommending RTL style.
# We deliberately create two reset arcs in a single FSM so graph construction
# has to reuse the synthetic ANY reset pseudo-vertex rather than allocating it
# only once for a one-arc machine.
test.compile(verilator_flags2=['--cc --coverage-fsm'])

test.execute()

# Use annotated-source output so the golden proves both reset arcs remain
# visible and share the same synthetic ANY reset source.
test.run(cmd=[
    os.environ["VERILATOR_ROOT"] + "/bin/verilator_coverage",
    "--annotate",
    test.obj_dir + "/annotated",
    test.obj_dir + "/coverage.dat",
],
         verilator_run=True)

test.files_identical(test.obj_dir + "/annotated/" + test.name + ".v", test.golden_filename)

test.passes()
