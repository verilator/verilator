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

test.compile(verilator_flags2=['-trace'])

test.execute()

if test.vlt_all:
    test.file_grep(test.obj_dir + "/V" + test.name + "__Trace__0__Slow.cpp", r'c_trace_on\"')
    test.file_grep_not(test.obj_dir + "/V" + test.name + "__Trace__0__Slow.cpp", r'_trace_off\"')
    test.file_grep(test.trace_filename, r'\$enddefinitions')
    test.file_grep_not(test.trace_filename, r'inside_sub')

    test.vcd_identical(test.trace_filename, test.golden_filename)

test.passes()
