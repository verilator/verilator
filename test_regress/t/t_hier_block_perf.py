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
test.cycles = (int(test.benchmark) if test.benchmark else 1000000)
test.sim_time = test.cycles * 10 + 1000
THREADS = int(os.environ["SIM_THREADS"]) if "SIM_THREADS" in os.environ else 2

test.compile(benchmarksim=1,
             v_flags2=["+define+SIM_CYCLES=" + str(test.cycles), "--prof-exec", "--hierarchical"],
             threads=(THREADS if test.vltmt else 1))

test.execute(all_run_flags=[
    "+verilator+prof+exec+start+2",
    " +verilator+prof+exec+window+2",
    " +verilator+prof+exec+file+" + test.obj_dir + "/profile_exec.dat",
    " +verilator+prof+vlt+file+" + test.obj_dir + "/profile.vlt"])  # yapf:disable

test.run(cmd=[
    os.environ["VERILATOR_ROOT"] + "/bin/verilator_gantt", test.obj_dir +
    "/profile_exec.dat", "--vcd " + test.obj_dir + "/profile_exec.vcd", "| tee " + test.obj_dir +
    "/gantt.log"
])

test.passes()
