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
test.top_filename = "t/t_lint_assigneqexpr.v"

test.lint(verilator_flags2=['-Wall -Wno-DECLFILENAME'],
          fails=True,
          expect_filename=test.golden_filename)

test.extract(in_filename=test.top_filename,
             out_filename=test.root + "/docs/gen/ex_ASSIGNEQEXPR_faulty.rst",
             lines="26-29")

test.extract(in_filename=test.golden_filename,
             out_filename=test.root + "/docs/gen/ex_ASSIGNEQEXPR_msg.rst",
             lines="7-8")

test.passes()
