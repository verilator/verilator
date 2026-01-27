#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2024 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.priority(30)
test.scenarios('vlt_all')
test.top_filename = "t/t_hier_block.v"

# stats will be deleted but generation will be skipped if libs of hierarchical blocks exist.
test.clean_objs()

test.compile(verilator_flags2=[
    't/t_hier_block.cpp', '--stats', '--hierarchical', '--Wno-TIMESCALEMOD', '--CFLAGS',
    '"-pipe -DCPP_MACRO=cplusplus"', '--binary'
])

test.execute()

test.file_grep(test.obj_dir + "/Vsub0/sub0.sv", r'^\s+\/\/\s+timeprecision\s+(\d+)ps;', 1)
test.file_grep(test.obj_dir + "/Vsub0/sub0.sv", r'^module\s+(\S+)\s+', "sub0")
test.file_grep(test.obj_dir + "/Vsub1/sub1.sv", r'^module\s+(\S+)\s+', "sub1")
test.file_grep(test.obj_dir + "/Vsub2/sub2.sv", r'^module\s+(\S+)\s+', "sub2")
test.file_grep(test.stats, r'HierBlock,\s+Hierarchical blocks\s+(\d+)', 14)
test.file_grep(test.run_log_filename, r'MACRO:(\S+) is defined', "cplusplus")

test.passes()
