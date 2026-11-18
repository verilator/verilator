#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt_all')
test.top_filename = "t/t_trace_dumpvars_scope.v"

test.compile(verilator_flags2=[
    "--binary", "--trace-vcd", "--protect-ids", "--protect-key", "DUMPVARS_TEST_KEY",
    "-Wno-INSECURE"
])
test.execute()

test.file_grep_count(test.trace_filename, r'\$var ', 18)
test.file_grep_not(test.trace_filename, r' (?:esc\.inst|sub1a|sub1b|value|cyc) ')
for filename in test.glob_some(test.obj_dir + "/*.cpp"):
    test.file_grep_not(filename, r'esc\.inst')

test.passes()
