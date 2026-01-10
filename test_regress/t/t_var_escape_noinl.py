#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2026 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('simulator')
test.top_filename = "t/t_var_escape.v"
test.golden_filename = "t/t_var_escape.out"

test.compile(
    # Access is so we can dump waves
    v_flags2=['-trace' if test.vlt_all else ' +access+rwc', '-fno-inline'])

test.execute()

if test.vlt_all:
    test.file_grep(test.trace_filename, r'\$enddefinitions')
    sigre = re.escape("bra[ket]slash/dash-colon:9")
    test.file_grep(test.trace_filename, sigre)
    test.file_grep(test.trace_filename, r' other\.cyc ')
    test.file_grep(test.trace_filename, r' module mod\.with_dot ')
    test.vcd_identical(test.trace_filename, test.golden_filename)

test.passes()
