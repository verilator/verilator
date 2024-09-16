#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt_all')

# Verilator before 4.033 had 'double sc_time_stamp()', make sure new form compiles
test.vl_time_stamp64 = True

test.compile(verilator_flags2=['-DVL_TIME_STAMP64=1'])

test.execute()

test.passes()
