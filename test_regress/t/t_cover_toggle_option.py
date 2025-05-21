#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('simulator')

test.top_filename = "t/t_cover_toggle.v"

test.compile(verilator_flags2=['--cc --coverage --stats'])

test.execute()

# Read the input .v file and do any CHECK_COVER requests
test.inline_checks()

test.file_grep_not(test.obj_dir + "/coverage.dat", "largeish")

if test.vlt_all:
    test.file_grep(test.stats, r'Coverage, Toggle points joined\s+(\d+)', 27)

test.run(cmd=[
    os.environ["VERILATOR_ROOT"] + "/bin/verilator_coverage",
    "--annotate",
    test.obj_dir + "/annotated",
    test.obj_dir + "/coverage.dat",
    "--filter-type toggle",
],
         verilator_run=True)

test.files_identical(test.obj_dir + "/annotated/t_cover_toggle.v", test.golden_filename)

test.run(cmd=[
    os.environ["VERILATOR_ROOT"] + "/bin/verilator_coverage",
    "--annotate-points",
    "--annotate",
    test.obj_dir + "/annotated-points",
    test.obj_dir + "/coverage.dat",
    "--filter-type toggle",
],
         verilator_run=True)

test.files_identical(test.obj_dir + "/annotated-points/t_cover_toggle.v",
                     "t/" + test.name + "__points.out")

test.passes()
