#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2025 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt')

test.top_filename = "t/t_property_sexpr_unsup.v"

test.lint(expect_filename=test.golden_filename,
          verilator_flags2=['-DPARSING_TIME', '--assert', '--timing', '--error-limit 1000'],
          fails=True)

test.passes()
