#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2025 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vltmt')
test.top_filename = "t/t_hier_block_perf.v"
cycles = 100000
test.sim_time = cycles * 10 + 1000

threads = 2
config_file = test.t_dir + "/" + test.name + ".vlt"
flags = [config_file, "--hierarchical", "-Wno-UNOPTFLAT", "-DSIM_CYCLES=" + str(cycles)]

test.compile(benchmarksim=1, v_flags2=["--prof-pgo"] + flags, threads=threads)

test.execute(all_run_flags=[
    "+verilator+prof+exec+start+0",
    " +verilator+prof+exec+file+/dev/null",
    " +verilator+prof+vlt+file+" + test.obj_dir + "/profile.vlt"])  # yapf:disable

test.file_grep(test.obj_dir + "/profile.vlt", r'profile_data -model "VTest"')
test.file_grep(test.obj_dir + "/profile.vlt", r'profile_data -model "V' + test.name + '"')

# Differentiate benchmarksim results
test.name = test.name + "_optimized"
test.compile(
    benchmarksim=1,
    # Intentionally no --prof-pgo here to make sure profile data can be read in
    # without it (that is: --prof-pgo has no effect on profile_data hash names)
    v_flags2=flags,
    threads=threads)

test.execute()

test.passes()
