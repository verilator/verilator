#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

#       irun -sv top.v t_dpi_export.v -cpost t_dpi_export_c.c -end

import vltest_bootstrap

test.scenarios('simulator')

test.compile(v_flags2=["t/t_dpi_export_c.cpp"],
             verilator_flags2=["-Wall -Wno-DECLFILENAME -no-l2name"])

test.execute()

test.passes()
