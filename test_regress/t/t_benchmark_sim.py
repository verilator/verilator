#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt')
test.top_filename = "t/t_gen_alw.v"  # Use any top file

# As an example, compile and simulate the top file with varying optimization level
l_opts = ['-O0', '-O1', '-O2', '-O3']

for l_opt in l_opts:
    test.compile(v_flags2=[l_opt])

    test.execute()

test.passes()
