#!/usr/bin/env python3
# DESCRIPTION: Verilator: FSM coverage of state registers with an enable, FSM coverage only
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import os

import vltest_bootstrap

test.scenarios('simulator')
test.top_filename = "t/t_cover_fsm_enable.v"

test.compile(verilator_flags2=['--cc --coverage-fsm'])

test.execute()

test.run(cmd=[
    os.environ["VERILATOR_ROOT"] + "/bin/verilator_coverage",
    "--annotate",
    test.obj_dir + "/annotated",
    test.obj_dir + "/coverage.dat",
],
         verilator_run=True)

test.files_identical(test.obj_dir + "/annotated/t_cover_fsm_enable.v", test.golden_filename)
test.file_grep_not(test.obj_dir + "/coverage.dat", r"t\.enable_u\.neither_q.*fsm_")
test.file_grep_not(test.obj_dir + "/coverage.dat", r"t\.enable_u\.nest_neither_q.*fsm_")
test.file_grep_not(test.obj_dir + "/coverage.dat", r"t\.enable_u\.reset_sel_q.*fsm_")
test.file_grep_not(test.obj_dir + "/coverage.dat", r"t\.enable_u\.other_hold_q.*fsm_")
test.file_grep_not(test.obj_dir + "/coverage.dat", r"t\.enable_u\.then_hold_q.*fsm_")

test.passes()
