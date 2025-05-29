#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2025 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vltmt')
test.clean_objs()

test.compile(
    v_flags2=["t/t_instr_count_dpi_large.cpp"],
    verilator_flags2=[
        "--instr-count-dpi 999999999",
        # Force UNOPTTHREADS error to cause Contraction limit increase beyond UINT32
        "--threads-max-mtasks 1",
        "-Wno-UNOPTTHREADS"
    ],
    threads=2)

test.execute()

test.passes()
