#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt_all')
test.top_filename = "t/t_timing_sched.v"

test.compile(verilator_flags2=["--exe --main --timing"])

test.execute(all_run_flags=["+verilator+debug"])

if not test.vltmt:  # vltmt output may vary between thread exec order
    test.files_identical(test.obj_dir + "/vlt_sim.log", test.golden_filename, "logfile")

test.passes()
