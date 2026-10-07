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
test.top_filename = "t/t_cover_fsm_expand.v"

test.compile(verilator_flags2=['--binary', '--coverage-fsm', '--coverage-fsm-expand', 'auto'])

test.execute(all_run_flags=["+verilator+coverage+file+" + test.coverage_filename])

test.run(cmd=[
    os.environ["VERILATOR_ROOT"] + "/bin/verilator_coverage",
    "--annotate",
    test.obj_dir + "/annotated",
    test.coverage_filename,
],
         verilator_run=True)

test.files_identical(test.obj_dir + "/annotated/" + test.top_filename[2:], test.golden_filename)

test.passes()
