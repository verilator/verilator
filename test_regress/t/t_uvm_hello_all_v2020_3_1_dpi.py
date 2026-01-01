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
test.pli_filename = "t/uvm/v2020_3_1/dpi/uvm_dpi.cc"

if test.have_dev_gcov:
    test.skip("Test suite intended for full dev coverage without needing this test")

test.compile(v_flags2=[
    "--binary",
    "--vpi",
    "-j 0",
    "--CFLAGS -O0",
    "-Wall",
    "+incdir+t/uvm",  #
    "t/uvm/uvm_pkg_all_v2020_3_1_dpi.svh",
    test.pli_filename
])

test.execute(all_run_flags=['' if test.verbose else '+UVM_NO_RELNOTES'])

test.file_grep(test.run_log_filename, r'UVM TEST PASSED')

test.passes()
