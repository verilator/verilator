#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt')

# This test documents a known Verilator timing limitation:
# Internal clocks (generated via `always #5 clk = ~clk`) don't properly
# trigger procedural blocks in --timing mode. Even explicit .sample() calls
# in always @(posedge clk) blocks don't execute.
#
# Root cause: Timing scheduler doesn't trigger NBA/active regions for
# internally generated clock edges.
#
# Workaround: Use module input clocks (see t_covergroup_auto_sample.v)
test.compile(verilator_flags2=["--timing"])

test.execute(fails=True, expect=r'%Error: .*Timeout')

test.passes()
