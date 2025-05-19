#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt')

test.compile(
    # We need to list verilated_vcd_c.cpp because without --trace Verilator
    # won't build it itself automatically.
    verilator_flags2=["--cc --exe", "t/" + test.name + "_c.cpp", "verilated_vcd_c.cpp"],
    make_top_shell=False,
    make_main=False)

test.execute(fails=True, expect_filename=test.golden_filename)

test.passes()
