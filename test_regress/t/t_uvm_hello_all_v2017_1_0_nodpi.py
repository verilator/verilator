#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.priority(50)
test.scenarios('vlt')
test.top_filename = 't/t_uvm_hello.v'

if test.have_dev_gcov:
    test.skip("Test suite intended for full dev coverage without needing this test")

test.compile(v_flags2=[
    "--binary",
    "-j 0",
    "-Wall",
    "+incdir+t/uvm",  #
    "t/uvm/uvm_pkg_all_v2017_1_0_nodpi.svh",
])

test.passes()
