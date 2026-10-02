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
test.top_filename = "t/t_forceable_array_sched.v"

test.compile(verilator_flags2=['--binary', '--vpi', '--vpi-lazy'])

test.file_grep(test.obj_dir + "/" + test.vm_prefix + "__Syms__Slow.cpp",
               r'forceableVarInsert\("nba_array", &\(TOP\.t__DOT__nba_array\)')

test.execute()

test.passes()
