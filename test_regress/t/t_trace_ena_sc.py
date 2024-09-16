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
test.top_filename = "t/t_trace_ena.v"

if not test.have_sc:
    test.skip("No SystemC installed")

test.compile(verilator_flags2=['-trace -sc'])

test.execute()

if test.vlt_all:
    # Note more checks in _cc.py
    test.file_grep(test.trace_filename, r'\$enddefinitions')

    test.vcd_identical(test.trace_filename, test.golden_filename)

test.passes()
