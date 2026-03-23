#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2024 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios("simulator")

test.compile(verilator_flags2=["--dump-tree"])

if test.vlt_all:
    # Test for correct array select width, see: #7012
    clean_tree = test.glob_one(test.obj_dir + "/V*_clean.tree")
    test.file_grep_count(clean_tree, r"ARRAYSEL.*G\/w16", 2)

test.execute()

test.passes()
