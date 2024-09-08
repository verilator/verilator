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
test.pli_filename = "t/t_vpi_var.cpp"

test.compile(make_top_shell=False,
             make_main=False,
             make_pli=True,
             sim_time=2100,
             iv_flags2=["-g2005-sv -D USE_VPI_NOT_DPI -DWAVES -DT_VPI_VAR2"],
             v_flags2=["+define+USE_VPI_NOT_DPI"],
             verilator_flags2=["--exe --vpi --no-l2name", test.pli_filename])

test.execute(use_libvpi=True, all_run_flags=['+PLUS +INT=1234 +STRSTR'])

test.passes()
