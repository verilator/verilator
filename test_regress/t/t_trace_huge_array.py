#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2024 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios("vlt_all")

test.compile(v_flags2=[
    "--trace-vcd --trace-max-width 0 --trace-max-array 0 --output-split-ctrace 10 --trace-structs"
])
trace_files = glob.glob(test.obj_dir + "/*Trace*.cpp")
if len(trace_files) < 10:
    test.error("Too few trace files")

test.execute()

test.passes()
