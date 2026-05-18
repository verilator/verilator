#!/usr/bin/env python3
# DESCRIPTION: Verilator: FSM coverage for fsm_register_wrapper state register wrappers
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import os

import vltest_bootstrap

test.scenarios('simulator')

test.compile(verilator_flags2=['--cc --coverage-fsm t/t_fsm_register_wrapper.vlt'])

test.execute()

test.run(
    cmd=[
        os.environ["VERILATOR_ROOT"] + "/bin/verilator_coverage",
        "--annotate",
        test.obj_dir + "/annotated",
        test.obj_dir + "/coverage.dat",
    ],
    verilator_run=True,
)

annotated_filename = test.obj_dir + "/annotated/" + test.name + ".v"
normalized_filename = test.obj_dir + "/annotated/" + test.name + ".normalized.v"
with open(annotated_filename, encoding="utf-8") as in_file:
    lines = [line.rstrip() for line in in_file]
while lines and not lines[-1]:
    lines.pop()
with open(normalized_filename, "w", encoding="utf-8") as out_file:
    for line in lines:
        out_file.write(line + "\n")

test.files_identical(normalized_filename, test.golden_filename)

test.passes()
