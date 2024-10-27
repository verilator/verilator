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
test.top_filename = "t/t_sys_sformat.v"

test.compile(
    # Avoid inlining our simple example, to make sure verilated.h works right
    verilator_flags2=["-O0"])

if re.search(r'clang', test.cxx_version):
    test.skip("Known clang bug")
    #Here:   if (VL_UNLIKELY(VL_NEQ_W(12, __Vtemp1, vlSymsp->TOP__t.__PVT__str)))

test.execute()

test.passes()
