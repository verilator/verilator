#!/usr/bin/env python3
# DESCRIPTION: Verilator: FSM coverage with a compound reset and expression coverage
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import os
from pathlib import Path

import vltest_bootstrap

test.scenarios('simulator')
test.top_filename = "t/t_cover_fsm_compound_reset.v"

test.compile(verilator_flags2=["--cc --coverage-expr --coverage-fsm"])

test.execute()

test.run(cmd=[
    os.environ["VERILATOR_ROOT"] + "/bin/verilator_coverage",
    "--annotate",
    test.obj_dir + "/annotated",
    test.obj_dir + "/coverage.dat",
],
         verilator_run=True)

top = Path(test.top_filename)
test.files_identical(test.obj_dir + f"/annotated/{top.name}", test.golden_filename)

test.passes()
