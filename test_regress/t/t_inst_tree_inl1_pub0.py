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
test.top_filename = "t/t_inst_tree.v"

out_filename = test.obj_dir + "/V" + test.name + ".tree.json"

test.compile(v_flags2=[
    "--no-json-edit-nums", "-fno-dfg-post-inline", test.t_dir + "/t_inst_tree_inl1_pub0.vlt"
])

if test.vlt_all:
    test.file_grep(
        out_filename,
        r'{"type":"VAR","name":"t.u.u0.u0.z1",.*"loc":"f,70:[^"]*",.*"origName":"z1",.*"dtypeName":"logic"'
    )
    test.file_grep(
        out_filename,
        r'{"type":"VAR","name":"t.u.u0.u1.z1",.*"loc":"f,70:[^"]*",.*"origName":"z1",.*"dtypeName":"logic"'
    )
    test.file_grep(
        out_filename,
        r'{"type":"VAR","name":"t.u.u1.u0.z0",.*"loc":"f,70:[^"]*",.*"origName":"z0",.*"dtypeName":"logic"'
    )

test.execute(expect=r"\] (%m|.*t\.ps): Clocked\n")

test.passes()
