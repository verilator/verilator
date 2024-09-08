#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vltmt')
test.top_filename = "t/t_verilated_all.v"

root = ".."

test.compile(
    # Can't use --coverage and --savable together, so cheat and compile inline
    verilator_flags2=[
        "--cc --coverage-toggle --coverage-line --coverage-user --trace --vpi " + root +
        "/include/verilated_save.cpp",
        ("--timing" if test.have_coroutines else "--no-timing -Wno-STMTDLY")
    ],
    threads=1)

test.execute()

test.passes()
