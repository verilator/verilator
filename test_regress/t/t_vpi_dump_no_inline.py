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
test.pli_filename = "t/t_vpi_dump.cpp"
test.golden_filename = "t/t_vpi_dump.out"
test.top_filename = "t/t_vpi_dump.v"

test.compile(make_top_shell=False,
             make_main=False,
             make_pli=True,
             iv_flags2=["-g2005-sv"],
             verilator_flags2=[
                 "--exe --vpi --public-flat-rw --no-l2name --fno-inline", test.pli_filename,
                 "t/TestVpiMain.cpp"
             ],
             make_flags=['CPPFLAGS_ADD=-DVL_NO_LEGACY'])

test.execute(use_libvpi=True,
             expect_filename=test.golden_filename,
             xrun_run_expect_filename=re.sub(r'\.out$', '.xrun.out', test.golden_filename),
             iv_run_expect_filename=re.sub(r'\.out$', '.iv.out', test.golden_filename))

test.passes()
