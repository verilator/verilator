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

# --vpi-lazy + --coverage used to abort at compile.
test.top_filename = "t/t_vpi_lazy_trace.v"
test.pli_filename = "t/t_vpi_lazy_trace.cpp"

test.compile(make_top_shell=False,
             make_main=False,
             verilator_flags2=[
                 "--exe --vpi --vpi-lazy --coverage --no-l2name"
                 " --debug --dump-tree=9 --stats", test.pli_filename
             ])

test.execute()

test.passes()
