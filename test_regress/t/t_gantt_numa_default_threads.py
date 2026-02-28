#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import os
import sys
import vltest_bootstrap

test.scenarios('vltmt')

test.top_filename = "t/t_gantt.v"
test.pli_filename = "t/t_gantt_numa_default_threads.cpp"

# Require enough cores so default thread count stays >= model threads
# (we don't call contextp->threads in this test)
test.skip_if_too_few_cores()

test.compile(
    make_main=False,
    verilator_flags2=[
        "--prof-exec",
        "--exe",
        test.pli_filename,
        test.t_dir + "/t_gantt_c.cpp",
    ],
    threads=test.get_default_vltmt_threads,
)

test.execute(all_run_flags=[
    "+verilator+prof+exec+start+2",
    " +verilator+prof+exec+window+2",
    " +verilator+prof+exec+file+" + test.obj_dir + "/profile_exec.dat",
])

gantt_log = test.obj_dir + "/gantt_default_threads.log"
test.run(cmd=[
    os.environ["VERILATOR_ROOT"] + "/bin/verilator_gantt",
    "--no-vcd",
    test.obj_dir + "/profile_exec.dat",
    "| tee " + gantt_log,
])

if sys.platform != "darwin":
    test.file_grep(gantt_log, r"NUMA status += NUMA assignment not requested")

test.passes()
