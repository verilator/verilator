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
test.top_filename = "t/t_dpi_var.v"

out_filename = test.obj_dir + "/V" + test.name + ".tree.json"

test.compile(make_top_shell=False,
             make_main=False,
             verilator_flags2=[
                 "--no-json-edit-nums", "--exe --no-l2name", test.t_dir + "/t_dpi_var.vlt",
                 test.t_dir + "/t_dpi_var.cpp"
             ])

if test.vlt_all:
    test.file_grep(
        out_filename,
        r'{"type":"VAR","name":"formatted","addr":"[^"]*","loc":"\w,58:[^"]*",.*"origName":"formatted",.*"direction":"INPUT",.*"dtypeName":"string",.*"attrSFormat":true'
    )
    test.file_grep(
        out_filename,
        r'{"type":"VAR","name":"t.sub.in","addr":"[^"]*","loc":"\w,81:[^"]*",.*"origName":"in",.*"dtypeName":"int",.*"isSigUserRdPublic":true'
    )
    test.file_grep(
        out_filename,
        r'{"type":"VAR","name":"t.sub.fr_a","addr":"[^"]*","loc":"\w,82:[^"]*",.*"origName":"fr_a",.*"dtypeName":"int",.*"isSigUserRdPublic":true,.*"isSigUserRWPublic":true'
    )
    test.file_grep(
        out_filename,
        r'{"type":"VAR","name":"t.sub.fr_b","addr":"[^"]*","loc":"\w,83:[^"]*",.*"origName":"fr_b",.*"dtypeName":"int",.*"isSigUserRdPublic":true,.*"isSigUserRWPublic":true'
    )

test.execute()

test.passes()
