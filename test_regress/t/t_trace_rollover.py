#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt_all')
test.top_filename = "t_trace_cat.v"

test.compile(make_top_shell=False, make_main=False, v_flags2=["--trace --exe", test.pli_filename])

test.execute()

os.system("cat " + test.obj_dir + "/simrollover_cat*.vcd " + " > " + test.obj_dir + "/simall.vcd")

test.vcd_identical(test.obj_dir + "/simall.vcd", test.golden_filename)

test.file_grep_not(test.obj_dir + "/simrollover_cat0000.vcd", r'^#')
test.file_grep(test.obj_dir + "/simrollover_cat0001.vcd", r'^#')
test.file_grep(test.obj_dir + "/simrollover_cat0002.vcd", r'^#')

test.passes()
