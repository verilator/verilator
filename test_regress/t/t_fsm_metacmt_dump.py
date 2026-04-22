#!/usr/bin/env python3
# DESCRIPTION: Verilator: FSM metacomment dump test
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import json

import vltest_bootstrap

test.scenarios('vlt')

test.top_filename = "t/t_fsm_metacmt_dump.v"

test.lint(v_flags=["--dump-tree --dump-tree-json --no-json-edit-nums"])

tree_files = test.glob_some(test.obj_dir + "/*.tree")
json_files = test.glob_some(test.obj_dir + "/*.tree.json")

test.file_grep_any(tree_files, r'\[aFSMSTATE\]')
test.file_grep_any(tree_files, r'\[aFSMRESETARC\]')
test.file_grep_any(tree_files, r'\[aFSMARCCOND\]')

test.file_grep_any(json_files, r'"attrFsmState":true')
test.file_grep_any(json_files, r'"attrFsmResetArc":true')
test.file_grep_any(json_files, r'"attrFsmArcInclCond":true')

for filename in json_files:
    with open(filename, 'r', encoding="utf8") as fh:
        json.load(fh)

test.passes()
