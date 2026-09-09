#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt_all')
test.sim_time = 2000000

test.top_filename = "t/t_dfg_break_cycles_deep.v"

# Compile reference (no DFG optimization)
test.compile(verilator_flags2=[
    "--stats",
    "--build",
    "-fno-dfg",
    "-fno-gate",
    "-Mdir", test.obj_dir + "/obj_ref",
    "--prefix", "Vref",
    "-Wno-UNOPTFLAT"
])

# Compile optimized with DFG break cycles
test.compile(verilator_flags2=[
    "--stats",
    "--build",
    "--exe",
    "-fno-gate",
    "-Mdir", test.obj_dir + "/obj_opt",
    "--prefix", "Vopt",
    "-Wno-UNOPTFLAT",
    "--debugi-V3DfgBreakCycles", "9",
    "../obj_ref/Vref__ALL.a",
    "../../t/t_dfg_break_cycles_deep.cpp"
])

# Execute test
test.execute(executable=test.obj_dir + "/obj_opt/Vopt")

test.passes()
