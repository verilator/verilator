#!/usr/bin/env python3
# DESCRIPTION: Verilator: Subgraph boundary is disabled by default
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import json

import vltest_bootstrap

test.scenarios('vlt')
test.top_filename = "t/t_subgraph_boundary.v"

tree_filename = test.obj_dir + "/V" + test.name + "_010_linkdotparam.tree.json"
root_header = test.obj_dir + "/V" + test.name + "___024root.h"

test.compile(verilator_flags2=["--dump-tree-json", "--no-json-edit-nums"])
test.execute()

test.file_grep_not(tree_filename, r'"subgraphBoundary":true')
test.file_grep_not(root_header, r'sg_rotate\* __PVT__t__DOT__i_a;')

with open(tree_filename, 'r', encoding="utf8") as fh:
    json.load(fh)

test.passes()
