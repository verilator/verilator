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
test.top_filename = "t/t_assert_basic.v"

test.compile(v_flags2=[
    '+define+FAILING_ASSERTIONS', ('--assert' if test.vlt_all else ('+assert' if test.nc else ''))
],
             fails=test.nc)

test.execute(fails=test.vlt_all)

test.passes()
