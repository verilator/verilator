#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2025 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt_all')
test.init_benchmarksim()
test.cycles = (int(test.benchmark) if test.benchmark else 100000)
test.sim_time = test.cycles * 10 + 1000

THREADS = 2
HIER_BLOCK_THREADS = 2
HIER_THREADS = 4

config_file = test.t_dir + "/" + test.name + ".vlt"

test.compile(
    benchmarksim=1,
    v_flags2=[
        config_file, "+define+SIM_CYCLES=" + str(test.cycles), "--hierarchical", "--stats",
        "-Wno-UNOPTFLAT",
        (f"-DWORKERS={HIER_BLOCK_THREADS}" if test.vltmt and HIER_BLOCK_THREADS > 1 else ""),
        (f"--hierarchical-threads {HIER_THREADS}" if test.vltmt and HIER_THREADS > 1 else "")
    ],
    threads=(THREADS if test.vltmt else 1),
    context_threads=(max(HIER_THREADS, THREADS) if test.vltmt else 1))

if test.vltmt:
    test.file_grep(test.obj_dir + "/V" + test.name + "__hier.dir/V" + test.name + "__stats.txt",
                   r'Optimizations, Thread schedule count\s+(\d+)', 1)
    test.file_grep(test.obj_dir + "/V" + test.name + "__hier.dir/V" + test.name + "__stats.txt",
                   r'Optimizations, Thread schedule total tasks\s+(\d+)', 2)

test.execute()

test.passes()
