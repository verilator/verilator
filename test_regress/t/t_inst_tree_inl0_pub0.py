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
test.top_filename = "t/t_inst_tree.v"

out_filename = test.obj_dir + "/V" + test.name + ".tree.json"

test.compile(v_flags2=["--no-json-edit-nums", test.t_dir + "/" + test.name + ".vlt"])

if test.vlt_all:
    test.file_grep(out_filename,
                   r'{"type":"MODULE","name":"l1",.*"loc":"\w,56:[^"]*",.*"origName":"l1"')
    test.file_grep(out_filename,
                   r'{"type":"MODULE","name":"l2",.*"loc":"\w,62:[^"]*",.*"origName":"l2"')
    test.file_grep(out_filename,
                   r'{"type":"MODULE","name":"l3",.*"loc":"\w,69:[^"]*",.*"origName":"l3"')
    # l4 and l5 hold nothing but combinational logic feeding their single reader,
    # so they are optimized away entirely, even though they are marked no_inline
    test.file_grep_not(out_filename, r'{"type":"MODULE","name":"l4"')
    test.file_grep_not(out_filename, r'{"type":"MODULE","name":"l5__P')

test.execute()
test.file_grep(test.run_log_filename, r"\] (%m|.*t\.ps): Clocked")

test.passes()
