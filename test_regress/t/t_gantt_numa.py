#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

# Test for bin/verilator_gantt,

import vltest_bootstrap

test.scenarios('vltmt')
test.top_filename = "t/t_gen_alw.v"  # Any, as long as runs a few cycles

test.compile(
    v_flags2=["--prof-exec"],
    # Checks below care about thread count
    threads=4)

# We need several experiments to make sure that the algorithm is working
trials = 4
for trial in range(0, trials):
    print("--------- Trial %d" % trial)

    test.execute(  # Test fail: run_env='numactl -m 0 -C 0,0,0,0',
        all_run_flags=[
            "+verilator+prof+exec+start+2", " +verilator+prof+exec+window+2",
            " +verilator+prof+exec+file+" + test.obj_dir + "/profile_exec.dat"
        ])

    gantt_log = test.obj_dir + "/gantt.log"

    test.run(cmd=[
        os.environ["VERILATOR_ROOT"] + "/bin/verilator_gantt", "--no-vcd", test.obj_dir +
        "/profile_exec.dat", "| tee " + gantt_log
    ])

    test.file_grep(gantt_log, r'CPU info:')
    test.file_grep(gantt_log, r'NUMA status += assigned')
    # False fails occasionally
    # test.file_grep_not(gantt_log, r'%Warning:')  # e.g. There were fewer CPUs (1) than threads (3).

test.passes()
