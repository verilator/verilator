#!/usr/bin/env python3
# DESCRIPTION: Verilator: FSM coverage reset policy test
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

test.file_grep(test.obj_dir + "/coverage.dat", r"\[reset_include\]")
test.file_grep(test.obj_dir + "/coverage.dat", r"\[reset\]")

summary_default = test.run_capture(
    cmd=os.environ["VERILATOR_ROOT"] + "/bin/verilator_coverage " + test.obj_dir + "/coverage.dat")
summary_all = test.run_capture(
    cmd=os.environ["VERILATOR_ROOT"] + "/bin/verilator_coverage --include-reset-arcs "
        + test.obj_dir + "/coverage.dat")

if "fsm_arc" not in summary_default or "reset arcs:" not in summary_default:
    test.error("Expected reset arc disclosure in default FSM arc summary")
if "fsm_arc" not in summary_all:
    test.error("Expected FSM arc summary with --include-reset-arcs")

test.passes()
