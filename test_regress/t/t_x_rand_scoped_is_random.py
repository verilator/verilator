#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2025 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios("simulator_st")

test.compile(timing_loop=True, verilator_flags2=["--timing"])

filename = test.obj_dir + "/bits.log"

test.unlink_ok(filename)

for seed in range(1, 6):
    test.execute(all_run_flags=["+verilator+rand+reset+2", f"+verilator+seed+{seed}"])

unique_strings = set()

with open(filename, "r", encoding="utf-8") as file:
    for line in file:
        unique_strings.update(line.split())

count_unique_strings = len(unique_strings)

# A ideal random generator has a fail chance of 1 in 66 million
expected_unique_strings = 4
if count_unique_strings < expected_unique_strings:
    test.error(
        f"Expected at least {expected_unique_strings} unique strings, got {count_unique_strings}")

test.passes()
