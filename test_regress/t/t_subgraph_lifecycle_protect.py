#!/usr/bin/env python3
# DESCRIPTION: Verilator: Subgraph boundary identities across compiler stages
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt')
test.top_filename = "t/t_subgraph_lifecycle.v"
test.compile(verilator_flags2=["--subgraph-schedule", "--stats", "--protect-ids"])
test.execute()
test.file_grep(test.stats, r'Subgraph boundary, delayed publications\s+(\d+)', 3)
metadata = test.obj_dir + "/" + test.vm_prefix + "__subgraph_boundary.txt"
with open(metadata, encoding='utf8') as fh:
    contents = fh.read()
if any(name in contents for name in ('sg_lifecycle', 'cycles', 'i_a', 'i_b', 'i_c')):
    test.error("Boundary metadata exposed an unprotected design identifier")
test.passes()
