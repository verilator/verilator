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
test.top_filename = "t/t_const_opt.v"

# Run the same design as t_const_opt.py without bitopt tree optimization to make sure that the result is same.
test.compile(verilator_flags2=[
    "-Wno-UNOPTTHREADS", "--stats", "-fno-const-bit-op-tree", test.t_dir +
    "/t_const_opt.cpp", "-CFLAGS", "-Wno-tautological-compare"
])

test.execute()

test.passes()
