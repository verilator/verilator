#!/usr/bin/env python3
# DESCRIPTION: Verilator: FSM coverage basic test
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import os

import vltest_bootstrap

test.scenarios('simulator')

test.compile(verilator_flags2=['--cc --coverage'])

test.execute()

test.file_grep(test.obj_dir + "/coverage.dat", r"fsm_state")
test.file_grep(test.obj_dir + "/coverage.dat", r"fsm_arc")
test.file_grep(test.obj_dir + "/coverage.dat", r"S_IDLE")
test.file_grep(test.obj_dir + "/coverage.dat", r"S_IDLE->S_RUN")
test.file_grep(test.obj_dir + "/coverage.dat", r"\[reset_include\]")

summary = test.run_capture(
    cmd=os.environ["VERILATOR_ROOT"] + "/bin/verilator_coverage " + test.obj_dir + "/coverage.dat")
if "fsm_state" not in summary or "fsm_arc" not in summary:
    test.error("Expected FSM coverage rows in verilator_coverage summary")

test.passes()
