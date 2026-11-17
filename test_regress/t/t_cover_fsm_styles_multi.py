#!/usr/bin/env python3
# DESCRIPTION: Verilator: FSM coverage of the common FSM coding styles
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import os

import vltest_bootstrap

test.scenarios('simulator')

test.compile(verilator_flags2=['--cc', '--coverage-fsm', '--stats'])

test.execute()

test.run(cmd=[
    os.environ["VERILATOR_ROOT"] + "/bin/verilator_coverage",
    "--annotate",
    test.obj_dir + "/annotated",
    test.obj_dir + "/coverage.dat",
],
         verilator_run=True)

test.files_identical(test.obj_dir + "/annotated/" + test.name + ".v", test.golden_filename)

test.file_grep(test.stats, r'Coverage, FSM registers tried\s+(\d+)', 88)
test.file_grep(test.stats, r'Coverage, FSMs found\s+(\d+)', 57)
test.file_grep(test.stats, r'Coverage, FSM states\s+(\d+)', 168)
test.file_grep(test.stats, r'Coverage, FSM arcs\s+(\d+)', 200)
test.file_grep(test.stats, r'Coverage, FSM registers with too many paths\s+(\d+)', 1)

test.passes()
