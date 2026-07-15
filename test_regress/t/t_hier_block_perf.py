#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2025 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.priority(30)
test.scenarios('vlt_all')

test.cycles = (int(test.benchmark) if test.benchmark else 100000)
test.sim_time = test.cycles * 10 + 1000

THREADS = 2
HIER_BLOCK_THREADS = 2
HIER_THREADS = 4

config_file = test.t_dir + "/" + test.name + ".vlt"

test.compile(v_flags2=[
    config_file, "+define+SIM_CYCLES=" + str(test.cycles), "--prof-exec", "--hierarchical",
    "--stats", "-Wno-UNOPTFLAT",
    (f"-DWORKERS={HIER_BLOCK_THREADS}" if test.vltmt and HIER_BLOCK_THREADS > 1 else ""),
    (f"--hierarchical-threads {HIER_THREADS}" if test.vltmt and HIER_THREADS > 1 else "")
],
             threads=(THREADS if test.vltmt else 1),
             context_threads=(HIER_THREADS if test.vltmt else 1))

parent_stats = test.obj_dir + "/V" + test.name + "__hier.dir/V" + test.name + "__stats.txt"

test.file_grep(parent_stats, r'Finish, Guards\s+(\d+)', 8)
test.file_grep(parent_stats, r'Finish, Source scopes\s+(\d+)', 16)
test.file_grep(parent_stats, r'Optimizations, Hierarchical DPI wrappers with costs\s+(\d+)', 6)

test_wrapper = test.obj_dir + "/VTest/Test.sv"
for wrapper in ("check_hash", "combo_ignore", "combo_update", "create", "final", "seq_update"):
    test.file_grep(test_wrapper, r'no_finish -hier-dpi "Test_protectlib_' + wrapper + r'"')

check_wrapper = test.obj_dir + "/VCheck/Check.sv"
for wrapper in ("check_hash", "combo_ignore", "create", "final"):
    test.file_grep(check_wrapper, r'no_finish -hier-dpi "Check_protectlib_' + wrapper + r'"')
for wrapper in ("combo_update", "seq_update"):
    test.file_grep_not(check_wrapper, r'no_finish -hier-dpi "Check_protectlib_' + wrapper + r'"')

if test.vltmt:
    test.file_grep(parent_stats, r'Optimizations, Thread schedule count\s+(\d+)', 2)
    test.file_grep(parent_stats, r'Optimizations, Thread schedule total tasks\s+(\d+)', 3)

test.execute(all_run_flags=[
    "+verilator+prof+exec+start+2",
    " +verilator+prof+exec+window+2",
    " +verilator+prof+exec+file+" + test.obj_dir + "/profile_exec.dat",
    " +verilator+prof+vlt+file+" + test.obj_dir + "/profile.vlt"])  # yapf:disable

gantt_log = test.obj_dir + "/gantt.log"

test.run(cmd=[
    os.environ["VERILATOR_ROOT"] + "/bin/verilator_gantt", test.obj_dir +
    "/profile_exec.dat", "--vcd " + test.obj_dir + "/profile_exec.vcd", "| tee " + gantt_log
])

test.passes()
