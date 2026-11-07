#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2024 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.priority(100)
test.scenarios('vlt')
test.top_filename = "t/t_EXAMPLE.v"

test.compile(verilator_flags2=['--debug-self-test'],
             verilator_make_gmake=False,
             make_top_shell=False,
             make_main=False)

# Test static assertion termination without calling into compiler global cleanup.
# Use the real checked VNUser conversions and instrument the header in coverage builds.
executable = test.obj_dir + "/user_slots"
flags = "--coverage -DVL_GCOV" if test.have_dev_gcov else ""
if test.have_dev_asan:
    flags += " -fsanitize=address"
test.run(cmd=[
    os.environ['CXX'], "-std=c++17", "-pthread", flags, "-I" + test.root + "/include",
    "-I" + test.root + "/src", "-I" + test.root + "/src/obj_dbg",
    "t/t_a3_selftest.cpp", "-o", executable
])
test.run(cmd=[executable], logfile=test.obj_dir + "/slots_valid.log")
for mode, golden in [("integer", "t/t_a3_selftest_integer.out"),
                     ("pointer", "t/t_a3_selftest_pointer.out"),
                     ("worker", "t/t_a3_selftest_integer.out")]:
    test.run(cmd=[executable, mode], fails='any',
             logfile=test.obj_dir + "/slots_" + mode + ".log", expect_filename=golden)

test.passes()
