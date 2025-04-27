#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt_all')
test.top_filename = "t/t_hier_block.v"

# CI environment offers 2 VCPUs, 2 thread setting causes the following warning.
# %Warning-UNOPTTHREADS: Thread scheduler is unable to provide requested parallelism; consider asking for fewer threads.
# So use 6 threads here though it's not optimal in performance, but ok.

test.compile(
    v_flags2=['t/t_hier_block.cpp'],
    verilator_flags2=[
        '--hierarchical',
        '--Wno-TIMESCALEMOD',
        '--trace-vcd',
        '--no-trace-underscore',  # To avoid handle mismatches
    ],
    threads=(6 if test.vltmt else 1))

test.execute()

test.vcd_identical(test.trace_filename, test.golden_filename)

test.passes()
