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

test.compile(
    v_flags2=[
        "--binary --timing -j 0 +incdir+t/uvm",  #
        "--error-limit 200 --debug-exit-uvm"
    ],
    verilator_make_gmake=False)

#test.execute()

test.passes()
