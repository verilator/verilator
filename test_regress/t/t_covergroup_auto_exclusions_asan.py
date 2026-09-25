#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap
import coverage_covergroup_common

test.scenarios('vlt')
test.top_filename = 't/t_covergroup_auto_exclusions.v'
test.golden_filename = 't/t_covergroup_auto_exclusions.out'

if test.tsan:
    test.skip("ThreadSanitizer not compatible with AddressSanitizer\n")

# Construction-time value analysis and dynamic cross layouts under AddressSanitizer
coverage_covergroup_common.run(
    test, verilator_flags2=['--timing', '-CFLAGS -fsanitize=address -LDFLAGS -fsanitize=address'])

test.passes()
