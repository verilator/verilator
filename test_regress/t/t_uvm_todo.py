#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt')

if test.have_dev_gcov:
    test.skip("Test suite intended for full dev coverage without needing this test")

test.compile(v_flags2=["--timing", "+incdir+t/uvm", "t/t_uvm_todo.vlt", "-j 0"],
             make_flags=['-k'],
             verilator_make_gmake=False)

test.passes()
