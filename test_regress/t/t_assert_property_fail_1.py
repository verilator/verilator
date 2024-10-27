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
test.top_filename = "t/t_assert_property.v"

test.compile(v_flags2=['+define+FAIL_ASSERT_1'], verilator_flags2=['--assert --cc'])

test.execute()

# We expect to get a message when this assert fires:
test.file_grep(test.run_log_filename, r'cyc != 3')

test.passes()
