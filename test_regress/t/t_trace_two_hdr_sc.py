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
test.top_filename = "t_trace_two_a.v"

if not test.have_sc:
    test.skip("No SystemC installed")

test.compile(make_main=False,
             verilator_make_gmake=False,
             top_filename='t_trace_two_b.v',
             vm_prefix='Vt_trace_two_b',
             verilator_flags2=['-sc -trace'])

test.run(logfile=test.obj_dir + "/make_first_ALL.log",
         cmd=["make", "-C", test.obj_dir, "-f", "Vt_trace_two_b.mk", "Vt_trace_two_b__ALL.cpp"])

test.compile(make_main=False,
             top_filename='t_trace_two_a.v',
             make_flags=['CPPFLAGS_ADD=-DTEST_HDR_TRACE'],
             verilator_flags2=['-sc', '-exe', '-trace', test.t_dir + "/t_trace_two_sc.cpp"])

test.execute()

if test.vlt_all:
    test.file_grep(test.trace_filename, r'\$enddefinitions')
    test.vcd_identical(test.trace_filename, test.golden_filename)

test.passes()
