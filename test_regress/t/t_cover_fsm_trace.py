#!/usr/bin/env python3
# DESCRIPTION: Verilator: One-process FSM coverage with traced counters
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import os

import vltest_bootstrap

test.scenarios('vlt')
test.top_filename = 't/t_vlcov_fsm_report.v'

test.compile(verilator_flags2=[
    '--coverage', '--trace-vcd', '--trace-coverage', '--dump-tree', '--dump-tree-json'
], )

# Generated trace counters must be identifiable in both AST dump formats.
test.file_grep(test.glob_one(test.obj_dir + '/*_coverage.tree'), r'\[COVERTRACE\]')
test.file_grep(test.glob_one(test.obj_dir + '/*_coverage.tree.json'), r'"isCoverageTrace":true')
test.execute()

test.run(cmd=[
    os.environ['VERILATOR_ROOT'] + '/bin/verilator_coverage',
    '--annotate',
    test.obj_dir + '/annotated',
    test.obj_dir + '/coverage.dat',
],
         verilator_run=True)

# Tracing must preserve the state and arc counts from the untraced test.
test.files_identical(test.obj_dir + '/annotated/t_vlcov_fsm_report.v', 't/t_vlcov_fsm_report.out')

test.passes()
