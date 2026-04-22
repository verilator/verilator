#!/usr/bin/env python3
# DESCRIPTION: Verilator: FSM coverage graph dump test
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vltmt')
test.top_filename = "t/t_cover_fsm_styles.v"

test.compile(v_flags2=["--coverage-fsm", "--dumpi-graph", "6"], threads=2)

dot_files = test.glob_some(test.obj_dir + "/*fsm_*.dot")
for dot_filename in dot_files:
    test.file_grep(dot_filename, r'digraph v3graph')

test.file_grep_any(dot_files, r'ANY')
test.file_grep_any(dot_files, r'default')

test.passes()
