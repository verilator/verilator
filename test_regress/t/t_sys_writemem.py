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
test.top_filename = "t/t_sys_readmem.v"

# Use random reset to ensure we're fully initializing arrays before
# $writememh, to avoid miscompares with X's on 4-state simulators.
test.verilated_randReset = 2  # 2 == truly random

# TODO make test more generic to take the data type as a define
# then we can call test multiple times in different tests
test.compile(v_flags2=[
    '+define+WRITEMEM_READ_BACK=1',
    '\'+define+OUT_TMP1=\"' + test.obj_dir + '/tmp1.mem\"\'',
    '\'+define+OUT_TMP2=\"' + test.obj_dir + '/tmp2.mem\"\'',
    '\'+define+OUT_TMP3=\"' + test.obj_dir + '/tmp3.mem\"\'',
    '\'+define+OUT_TMP4=\"' + test.obj_dir + '/tmp4.mem\"\'',
    '\'+define+OUT_TMP5=\"' + test.obj_dir + '/tmp5.mem\"\'',
    '\'+define+OUT_TMP6=\"' + test.obj_dir + '/tmp6.mem\"\'',
    '\'+define+OUT_TMP7=\"' + test.obj_dir + '/tmp7.mem\"\'',
    '\'+define+OUT_TMP8=\"' + test.obj_dir + '/tmp8.mem\"\'',
])

test.execute()

for i in range(1, 9):
    gold = test.t_dir + "/t_sys_writemem.gold" + str(i) + ".mem"
    out = test.obj_dir + "/tmp" + str(i) + ".mem"
    test.files_identical(out, gold)

test.passes()
