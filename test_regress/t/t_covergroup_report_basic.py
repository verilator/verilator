#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 OpenAI
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import os
from pathlib import Path

import vltest_bootstrap

test.scenarios('simulator')

test.compile(verilator_flags2=['--cc', '--coverage-user'])

test.execute()

test.files_identical_sorted(test.obj_dir + "/coverage.dat", "t/t_covergroup_report_basic.dat.out")

test.run(cmd=[
    os.environ["VERILATOR_ROOT"] + "/bin/verilator_coverage",
    "--annotate-points",
    "--annotate",
    test.obj_dir + "/annotated",
    test.obj_dir + "/coverage.dat",
],
         verilator_run=True)

top = Path(test.top_filename)
test.files_identical(test.obj_dir + f"/annotated/{top.name}",
                     "t/t_covergroup_report_basic.out")

test.passes()
