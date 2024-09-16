#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

# Test tracing with two models instanced
import vltest_bootstrap

test.scenarios('vlt_all')
test.top_filename = "t_trace_two_a.v"

test.compile(make_main=False,
             verilator_make_gmake=False,
             top_filename='t_trace_two_b.v',
             vm_prefix='Vt_trace_two_b',
             verilator_flags2=['--trace-fst --trace-threads 1'])

test.run(
    logfile=test.obj_dir + "/make_first_ALL.log",
    cmd=["make", "-C", "" + test.obj_dir, "-f", "Vt_trace_two_b.mk", "Vt_trace_two_b__ALL.cpp"])

test.compile(make_main=False,
             top_filename='t_trace_two_a.v',
             verilator_flags2=[
                 '-exe', '--trace-fst --trace-threads 1', '-DTEST_FST',
                 test.t_dir + "/t_trace_two_cc.cpp"
             ],
             v_flags2=['+define+TEST_DUMPPORTS'])

test.execute()

if test.vlt_all:
    test.fst_identical(test.trace_filename, test.golden_filename)

test.passes()
