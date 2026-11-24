#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt')
test.top_filename = "t/t_opt_bitblast_attr_bad.v"

# split_var on a variable only --vpi-lazy keeps does not blame 'public'
test.lint(fails=True,
          verilator_flags2=["--vpi-lazy"],
          expect_filename=test.golden_filename)

test.passes()
