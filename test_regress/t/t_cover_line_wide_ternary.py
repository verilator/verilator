#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap
from pathlib import Path

test.scenarios('simulator')

test.compile(verilator_flags2=['--cc', '--coverage-line'])

test.execute()

test.run(cmd=[
    os.environ["VERILATOR_ROOT"] + "/bin/verilator_coverage",
    "--annotate-points",
    "--annotate",
    test.obj_dir + "/annotated",
    test.obj_dir + "/coverage.dat",
],
         verilator_run=True)

top = Path(test.top_filename)
test.files_identical(test.obj_dir + f"/annotated/{top.name}", test.golden_filename)

test.passes()
