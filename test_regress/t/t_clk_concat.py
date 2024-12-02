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

out_filename = test.obj_dir + "/V" + test.name + ".tree.json"

test.compile(verilator_flags2=["+define+ATTRIBUTES --no-json-edit-nums"])

if test.vlt_all:
    test.file_grep(
        out_filename,
        r'{"type":"VAR","name":"clk0",.*"loc":"\w,74:[^"]*",.*"origName":"clk0",.*"direction":"INPUT",.*"isSigPublic":true,.*"attrClocker":"clker",.*"varType":"PORT",.*"dtypeName":"logic"'
    )
    test.file_grep(
        out_filename,
        r'{"type":"VAR","name":"clk1",.*"loc":"\w,75:[^"]*",.*"origName":"clk1",.*"direction":"INPUT",.*"isSigPublic":true,.*"attrClocker":"clker",.*"varType":"PORT",.*"dtypeName":"logic"'
    )
    test.file_grep(
        out_filename,
        r'{"type":"VAR","name":"clk2",.*"loc":"\w,76:[^"]*",.*"origName":"clk2",.*"direction":"INPUT",.*"isSigPublic":true,.*"attrClocker":"clker",.*"varType":"PORT",.*"dtypeName":"logic"'
    )

test.execute()

test.passes()
