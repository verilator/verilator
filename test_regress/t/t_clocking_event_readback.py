#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('simulator')

test.compile(verilator_flags2=["--binary", "--timing", "--vpi", "--bbox-sys"])

test.execute()

test.file_grep(test.run_log_filename, r'FIRST_RESULT d0=00000005 d1=00000005 d2=00000005')
test.file_grep(test.run_log_filename, r'SECOND_RESULT m0=00000005 m1=00000005 m2=00000005')

test.passes()
