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

test.compile(make_top_shell=False,
             make_main=False,
             sim_time=2100,
             v_flags2=["t/t_vpi_time_cb_c.cpp"],
             iv_flags2=["-g2005-sv -DWAVES -DIVERILOG"],
             verilator_flags2=["--exe --vpi --no-l2name", test.pli_filename])

test.execute()

test.passes()
