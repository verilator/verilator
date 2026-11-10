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

test.compile(verilator_flags2=["--binary", "--output-split-cfuncs", "1"])

test.execute()

files = [
    filename for filename in test.glob_some(test.obj_dir + "/" + test.vm_prefix + "*")
    if filename.endswith((".cpp", ".h"))
]
# The dump function was split
test.file_grep_any(files, r'___dump_triggers__act__0\(')
# Every declaration and definition of a dump function or piece is under VL_DEBUG
for filename in files:
    test.file_grep_not(filename, r'(?<!#ifdef VL_DEBUG\n)^\S.*___dump_triggers__\w+\(')

test.passes()
