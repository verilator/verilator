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
test.top_filename = "t/t_flag_make_cmake.v"

test.compile(  # Don't call cmake nor gmake from driver.py
    verilator_flags2=[
        '--exe --cc --build -j 2', '../' + test.main_filename, '-MAKEFLAGS -p --trace-vcd'
    ])

test.execute()

test.passes()
