#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap
import randomize_uniform_common

test.scenarios('simulator')

SOLUTIONS = [i for i in range(256) if bin(i).count('1') == 4]  # C(8,4) = 70

randomize_uniform_common.run(test, SOLUTIONS, r'\d+', key=int)
