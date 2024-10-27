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
test.top_filename = "t/t_opt_table_sparse.v"
test.golden_filename = "t/t_opt_table_sparse.out"


def check_splits(expected):
    n = 0
    for filename in test.glob_some(test.obj_dir + "/*.cpp"):
        if re.search(r'__ConstPool_', filename):
            n += 1
    if n != expected:
        test.error("__ConstPool*.cpp not split: " + str(n))


test.compile(verilator_flags2=["--stats", "--output-split 1"])

if test.vlt_all:
    test.file_grep(test.stats, r'Optimizations, Tables created\s+(\d+)', 1)
    test.file_grep(test.stats, r'ConstPool, Tables emitted\s+(\d+)', 2)

# Splitting should set VM_PARALLEL_BUILDS to 1 by default
test.file_grep(test.obj_dir + "/" + test.vm_prefix + "_classes.mk", r'VM_PARALLEL_BUILDS\s*=\s*1')

check_splits(2)

test.execute(expect_filename=test.golden_filename)

test.passes()
