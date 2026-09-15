#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('simulator')

test.sim_time = 2700

test.compile(
    timing_loop=True,
    verilator_flags2=['--assert', '--timing', '--coverage-user', '--dumpi-graph', '6', '--stats'])

if test.vlt_all:
    # Ring updates must not copy whole packed vectors.
    test.file_grep(test.stats, r'Optimizations, Expand, expanded wide words\s+(\d+)', 0)
    test.file_grep(test.stats, r'Optimizations, Expand, expanded wides\s+(\d+)', 0)

    # Keep the six wide rings bit-packed to avoid 32x storage.
    test.file_grep(test.stats,
                   r'Optimizations, Expand, pattern assign to sel var wide one bit\s+(\d+)', 6)

test.execute()

test.passes()
