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

test.compile(v_flags2=["--no-json-edit-nums", test.t_dir + "/t_func_dotted_inl0.vlt"])

if test.vlt_all:
    test.file_grep(
        out_filename,
        r'{"type":"MODULE","name":"ma",.*"loc":"\w,84:[^"]*",.*"origName":"ma",.*"modPublic":true')
    test.file_grep(
        out_filename,
        r'{"type":"MODULE","name":"mb",.*"loc":"\w,99:[^"]*",.*"origName":"mb",.*"modPublic":true')
    test.file_grep(
        out_filename,
        r'{"type":"MODULE","name":"mc",.*"loc":"\w,127:[^"]*",.*"origName":"mc",.*"modPublic":true'
    )
    test.file_grep(
        out_filename,
        r'{"type":"MODULE","name":"mc__PB1",.*"loc":"\w,127:[^"]*",.*"origName":"mc",.*"modPublic":true'
    )

test.execute()

test.passes()
