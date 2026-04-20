#!/usr/bin/env python3
# DESCRIPTION: Verilator: FSM reporting coverage test
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import os

import vltest_bootstrap

test.scenarios('simulator')

# This regression targets the reporting side of FSM coverage rather than the
# detector itself. The generated coverage.dat contains state points, ordinary
# arcs, default arcs, reset arcs, and reset-include arcs so verilator_coverage
# exercises the FSM-specific filtering and annotation code paths.
test.compile(verilator_flags2=['--cc --coverage'])

test.execute()

test.run(cmd=[
    os.environ["VERILATOR_ROOT"] + "/bin/verilator_coverage",
    "--write-info",
    test.obj_dir + "/coverage.info",
    test.obj_dir + "/coverage.dat",
],
         verilator_run=True)

test.file_grep(test.obj_dir + "/coverage.info", r"TN:verilator_coverage")
test.file_grep(test.obj_dir + "/coverage.info", r"BRF:")
test.file_grep(test.obj_dir + "/coverage.info", r"BRH:")

test.run(cmd=[os.environ["VERILATOR_ROOT"] + "/bin/verilator_coverage",
              "--annotate", test.obj_dir + "/annotated",
              test.obj_dir + "/coverage.dat"],
         verilator_run=True)  # yapf:disable

test.run(cmd=[os.environ["VERILATOR_ROOT"] + "/bin/verilator_coverage",
              "--include-reset-arcs",
              "--annotate", test.obj_dir + "/annotated-incl",
              test.obj_dir + "/coverage.dat"],
         verilator_run=True)  # yapf:disable

annotated = test.obj_dir + "/annotated/t_vlcov_fsm_report.v"
annotated_incl = test.obj_dir + "/annotated-incl/t_vlcov_fsm_report.v"

test.file_grep(annotated, r"FSM coverage")
test.file_grep(annotated, r"SYNTHETIC DEFAULT ARC")
test.file_grep(annotated, r"default->S0")
test.file_grep(annotated, r"\[reset arc, excluded from %\]")

test.file_grep(annotated_incl, r"FSM coverage")
test.file_grep(annotated_incl, r"\[reset_include\]")
test.file_grep_not(annotated_incl, r"\[reset arc, excluded from %\]")

test.passes()
