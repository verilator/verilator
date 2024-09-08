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
    "--no-json-edit-nums", "-fno-dfg-post-inline", "t/" + test.name +
    ".vlt", test.wno_unopthreads_for_few_cores
])

if test.vlt_all:
    test.file_grep(
        out_filename,
        r'{"type":"VAR","name":"u.u0.u0.z0",.*"loc":"f,70:[^"]*",.*"origName":"z0",.*"isSigPublic":true,.*"dtypeName":"logic",.*"isSigUserRdPublic":true.*"isSigUserRWPublic":true'
    )
    test.file_grep(
        out_filename,
        r'{"type":"VAR","name":"u.u0.u0.u0.u0.z1",.*"loc":"f,85:[^"]*",.*"origName":"z1",.*"isSigPublic":true,.*"dtypeName":"logic",.*"isSigUserRdPublic":true,.*"isSigUserRWPublic":true'
    )
    test.file_grep(
        out_filename,
        r'{"type":"VAR","name":"u.u0.u1.u0.u0.z",.*"loc":"f,83:[^"]*",.*"origName":"z",.*,"isSigPublic":true,.*dtypeName":"logic",.*"isSigUserRdPublic":true,.*"isSigUserRWPublic":true'
    )

test.execute(expect=r"\] (%m|.*t\.ps): Clocked")

test.passes()
