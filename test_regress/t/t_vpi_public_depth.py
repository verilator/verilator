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
             make_pli=True,
             iv_flags2=["-g2005-sv"],
             verilator_flags2=[
                 "+define+USE_DOLLAR_C32 --exe --vpi --no-l2name", test.pli_filename,
                 "--public-depth 3"
             ],
             make_flags=['CPPFLAGS_ADD=-DTEST_VPI_PUBLIC_DEPTH'])

test.execute(use_libvpi=True, v_flags2=[])

test.passes()
