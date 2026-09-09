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

# --public-flat-rw baseline for the t_vpi_lazy_gated_write design.
test.top_filename = "t/t_vpi_lazy_gated_write.v"
test.pli_filename = "t/t_vpi_lazy_gated_write.cpp"

test.compile(make_top_shell=False,
             make_main=False,
             verilator_flags2=[
                 "--exe --vpi --public-flat-rw --no-l2name", "-CFLAGS -DVL_TEST_UNGATED",
                 test.pli_filename
             ])

test.execute()

test.passes()
