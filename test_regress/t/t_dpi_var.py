#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2024 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('simulator')

out_filename = test.obj_dir + "/V" + test.name + ".tree.json"

test.compile(
    make_top_shell=False,
    make_main=False,
    verilator_flags2=["--no-json-edit-nums", "-DATTRIBUTES --exe --no-l2name", test.pli_filename])

if test.vlt_all:
    test.file_grep(
        out_filename,
        r'{"type":"VAR","name":"formatted",.*"loc":"\w,69:[^"]*",.*"origName":"formatted",.*"direction":"INPUT",.*"dtypeName":"string",.*"attrSFormat":true'
    )
    test.file_grep(
        out_filename,
        r'{"type":"VAR","name":"t.sub.in",.*"loc":"\w,91:[^"]*",.*"origName":"in",.*"dtypeName":"int",.*"isSigUserRdPublic":true'
    )
    test.file_grep(
        out_filename,
        r'{"type":"VAR","name":"t.sub.in_a",.*"loc":"\w,92:[^"]*",.*"origName":"in_a",.*"dtypeName":"int",.*"isSigUserRdPublic":true,.*"isSigUserRWPublic":true'
    )
    test.file_grep(
        out_filename,
        r'{"type":"VAR","name":"t.sub.in_b",.*"loc":"\w,93:[^"]*",.*"origName":"in_b",.*"dtypeName":"int",.*"isSigUserRdPublic":true,.*"isSigUserRWPublic":true'
    )
    test.file_grep(
        out_filename,
        r'{"type":"VAR","name":"t.sub.fr_a",.*"loc":"\w,94:[^"]*",.*"origName":"fr_a",.*"dtypeName":"int",.*"isSigUserRdPublic":true,.*"isSigUserRWPublic":true'
    )
    test.file_grep(
        out_filename,
        r'{"type":"VAR","name":"t.sub.fr_b",.*"loc":"\w,95:[^"]*",.*"origName":"fr_b",.*"dtypeName":"int",.*"isSigUserRdPublic":true,.*"isSigUserRWPublic":true'
    )

test.execute()

test.passes()
