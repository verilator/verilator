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
test.top_filename = "t/t_force_wide_sel.v"

test.compile(verilator_flags2=["--stats", "--vpi", "--vpi-lazy"])

# --vpi-lazy makes every signal public, so no force sel is narrowed
test.file_grep(test.stats, r'Non-overlapping force sels\s+(\d+)', 0)

test.file_grep(test.obj_dir + "/" + test.vm_prefix + "__Syms__Slow.cpp",
               r'forceableVarInsert\("selfSig", &\(TOP\.t__DOT__selfSig\)')

test.execute()

test.passes()
