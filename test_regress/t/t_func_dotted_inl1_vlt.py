#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('simulator')
test.top_filename = "t/t_func_dotted.v"

out_filename = test.obj_dir + "/V" + test.name + ".tree.json"

test.compile(v_flags2=["--no-json-edit-nums", "t/t_func_dotted_inl1.vlt"])

if test.vlt_all:
    test.file_grep_not(out_filename, r'"ma0"')
    test.file_grep_not(out_filename, r'"mb0"')
    test.file_grep_not(out_filename, r'"mc0"')

test.execute()

test.passes()
