#!/usr/bin/env python3
# DESCRIPTION: Verilator: Program region scheduling with execution profiling
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt')
test.top_filename = "t/t_program_regions.v"

test.compile(verilator_flags2=["--binary", "--prof-exec"])

profile_filename = test.obj_dir + "/profile_exec.dat"
test.execute(all_run_flags=[
    "+verilator+prof+exec+start+0",
    "+verilator+prof+exec+window+8",
    "+verilator+prof+exec+file+" + profile_filename,
])

gantt_log = test.obj_dir + "/gantt.log"
test.run(cmd=[
    os.environ["VERILATOR_ROOT"] + "/bin/verilator_gantt", profile_filename, "--vcd",
    test.obj_dir + "/profile_exec.vcd"
],
         logfile=gantt_log)
test.file_grep(gantt_log, r'loop reinact')
test.file_grep(gantt_log, r'loop renba')

test.passes()
