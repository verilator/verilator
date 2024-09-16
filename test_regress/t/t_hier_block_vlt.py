#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt_all')
test.top_filename = "t/t_hier_block.v"

# stats will be deleted but generation will be skipped if libs of hierarchical blocks exist.
test.clean_objs()

# CI environment offers 2 VCPUs, 2 thread setting causes the following warning.
# %Warning-UNOPTTHREADS: Thread scheduler is unable to provide requested parallelism; consider asking for fewer threads.
# So use 6 threads here though it's not optimal in performance, but ok.
test.compile(v_flags2=['t/t_hier_block.cpp'],
             verilator_flags2=[
                 '--stats', '--hierarchical', '+define+SHOW_TIMESCALE', '+define+USE_VLT',
                 't/t_hier_block_vlt.vlt', '--CFLAGS', '"-pipe -DCPP_MACRO=cplusplus"'
             ],
             threads=(6 if test.vltmt else 1))

test.execute()

test.file_grep(test.obj_dir + "/Vsub0/sub0.sv", r'^\s+timeprecision\s+(\d+)ps;', 1)
test.file_grep(test.obj_dir + "/Vsub0/sub0.sv", r'^module\s+(\S+)\s+', "sub0")
test.file_grep(test.obj_dir + "/Vsub1/sub1.sv", r'^module\s+(\S+)\s+', "sub1")
test.file_grep(test.obj_dir + "/Vsub2/sub2.sv", r'^module\s+(\S+)\s+', "sub2")
test.file_grep(test.stats, r'HierBlock,\s+Hierarchical blocks\s+(\d+)', 14)
test.file_grep(test.run_log_filename, r'MACRO:(\S+) is defined', "cplusplus")

test.passes()
