#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt')
test.top_filename = "t/t_dump.v"

test.lint(v_flags=["--dump-tree-json --no-json-edit-nums"])

test.files_identical(test.obj_dir + "/Vt_dump_json_001_cells.tree.json", test.golden_filename,
                     'logfile')

test.passes()
