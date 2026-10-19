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
test.top_filename = "t/t_vpi_lazy.v"
test.pli_filename = "t/t_vpi_lazy.cpp"
test.golden_filename = "t/t_vpi_lazy.out"

# What is readable and writable must not depend on optimisation
test.compile(verilator_flags2=[
    "--exe --build --vpi-lazy --no-l2name -O0 -fno-const-before-dfg",
    f"-CFLAGS -DVM_PREFIX={test.vm_prefix}", test.pli_filename, "t/TestVpiMain.cpp"
])

test.execute(all_run_flags=["+verilator+rand+reset+1"], expect_filename=test.golden_filename)

test.passes()
