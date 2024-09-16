#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

# This test makes sure that the internal check of t_hier_block.v is correct.
# --hierarchical option is not set intentionally.

import vltest_bootstrap

# stats will be deleted but generation will be skipped if libs of hierarchical blocks exist.
test.clean_objs()

test.scenarios('vlt_all')
test.top_filename = "t/t_hier_block.v"

# CI environment offers 2 VCPUs, 2 thread setting causes the following warning.
# %Warning-UNOPTTHREADS: Thread scheduler is unable to provide requested parallelism; consider asking for fewer threads.
# So use 6 threads here though it's not optimal in performance, but ok.
test.compile(v_flags2=['t/t_hier_block.cpp'],
             verilator_flags2=[
                 '--stats', '+define+USE_VLT', 't/t_hier_block_vlt.vlt', '--CFLAGS',
                 '"-pipe -DCPP_MACRO=cplusplus"'
             ],
             threads=(6 if test.vltmt else 1))

test.execute()

test.file_grep_not(test.stats, r'HierBlock,\s+Hierarchical blocks\s+(\d+)')
test.file_grep(test.run_log_filename, r'MACRO:(\S+) is defined', "cplusplus")

test.passes()
