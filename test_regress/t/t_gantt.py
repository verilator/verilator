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

test.scenarios('vlt_all')
test.top_filename = "t/t_gen_alw.v"  # Any, as long as runs a few cycles

test.compile(
    v_flags2=["--prof-exec"],
    # Checks below care about thread count, so use 2 (minimum reasonable)
    threads=(2 if test.vltmt else 1))

test.execute(all_run_flags=[
    "+verilator+prof+exec+start+2",
    " +verilator+prof+exec+window+2",
    " +verilator+prof+exec+file+" + test.obj_dir + "/profile_exec.dat",
    " +verilator+prof+vlt+file+" + test.obj_dir + "/profile.vlt"])  # yapf:disable

# The profiling data goes direct to the runtime's STDOUT
#  (maybe that should go to a separate file - gantt.dat?)
gantt_log = test.obj_dir + "/gantt.log"

test.run(cmd=[
    os.environ["VERILATOR_ROOT"] + "/bin/verilator_gantt", test.obj_dir +
    "/profile_exec.dat", "--vcd " + test.obj_dir + "/profile_exec.vcd", "| tee " + gantt_log
])

if test.vltmt:
    test.file_grep(gantt_log, r'Total threads += 2')
    test.file_grep(gantt_log, r'Total mtasks += 7')
    # Predicted thread utilization should be less than 100%
    test.file_grep_not(gantt_log, r'Thread utilization =\s*\d\d\d+\.\d+%')
else:
    test.file_grep(gantt_log, r'Total threads += 1')
    test.file_grep(gantt_log, r'Total mtasks += 0')

test.file_grep(gantt_log, r'\|\s+2\s+\|\s+2\.0+\s+\|\s+eval')

# Diff to itself, just to check parsing
test.vcd_identical(test.obj_dir + "/profile_exec.vcd", test.obj_dir + "/profile_exec.vcd")

test.passes()
