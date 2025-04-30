#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios("simulator")

test.compile(verilator_flags2=["--x-initial unique"])

test.execute(
    all_run_flags=["+verilator+rand+reset+2"], expect_filename=test.golden_filename
)

test.passes()

other_logs = glob.glob("t/t_x_rand_stability_*.out")
for other_log in other_logs:
    test.files_identical(test.golden_filename, other_log)
