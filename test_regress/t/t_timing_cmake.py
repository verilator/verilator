#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('simulator')
test.top_filename = "t/t_timing_events.v"

if not test.have_coroutines:
    test.skip("No coroutine support")
if not test.have_cmake:
    test.skip("cmake is not installed")

test.compile(verilator_flags2=["--timescale 10ns/1ns --main --timing"],
             verilator_make_gmake=False,
             verilator_make_cmake=True)

test.passes()
