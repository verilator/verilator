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

test.compile(v_flags2=["--no-json-edit-nums", "t/t_func_dotted_inl2.vlt"])

if test.vlt_all:
    modps = test.file_grep(
        out_filename,
        r'{"type":"MODULE","name":"mb","addr":"([^"]*)","loc":"f,99:[^"]*",.*"origName":"mb"')
    modp = modps[0][0]
    test.file_grep(
        out_filename,
        r'{"type":"CELL","name":"t.ma0.mb0","addr":"[^"]*","loc":"f,87:[^"]*",.*"origName":"mb0",.*"modp":"([^"]*)"',
        modp)

test.execute()

test.passes()
