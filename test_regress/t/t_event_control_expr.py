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

test.compile(
    # do not test classes for multithreaded, as V3InstrCount doesn't handle MemberSel
    verilator_flags2=(['-DNO_CLASS'] if test.vltmt else []))

test.execute()

for filename in test.glob_some(test.obj_dir + "/" + test.vm_prefix + "*.cpp"):
    # Check that these simple expressions are not stored in temp variables
    test.file_grep_not(filename, r'__Vtrigcurr__expression_.* = vlSelf->clk;')
    test.file_grep_not(filename, r'__Vtrigcurr__expression_.* = vlSelf->t__DOT__q.at\(0U\);')
    test.file_grep_not(filename,
                       r'__Vtrigcurr__expression_.* = .*vlSelf->t__DOT____Vcellinp__u_array__t')
    test.file_grep_not(filename,
                       r'__Vtrigcurr__expression_.* = .*vlSymsp->TOP__t__DOT__u_class.__PVT__obj')
    # The line below should only be generated if concats/replicates aren't converted to separate senitems
    test.file_grep_not(filename, r'__Vtrigcurr__expression_.* = .*vlSelf->t__DOT__a')

test.passes()
