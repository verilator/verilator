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

test.compile(v_flags2=["--no-json-edit-nums", test.t_dir + "/" + test.name + ".vlt"])

if test.vlt_all:
    test.file_grep(out_filename,
                   r'{"type":"MODULE","name":"l1",.*"loc":"f,56:[^"]*",.*"origName":"l1"')
    test.file_grep(out_filename,
                   r'{"type":"MODULE","name":"l2",.*"loc":"f,62:[^"]*",.*"origName":"l2"')
    test.file_grep(out_filename,
                   r'{"type":"MODULE","name":"l3",.*"loc":"f,69:[^"]*",.*"origName":"l3"')
    test.file_grep(out_filename,
                   r'{"type":"MODULE","name":"l4",.*"loc":"f,76:[^"]*",.*"origName":"l4"')
    test.file_grep(out_filename,
                   r'{"type":"MODULE","name":"l5__P1",.*"loc":"f,83:[^"]*",.*"origName":"l5"')
    test.file_grep(out_filename,
                   r'{"type":"MODULE","name":"l5__P2",.*"loc":"f,83:[^"]*",.*"origName":"l5"')

test.execute(expect=r"\] (%m|.*t\.ps): Clocked", )

test.passes()
