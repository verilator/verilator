#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('linter')

test.twostate_capable = False
test.fourstate_nowarn = False

test.top_filename = "t/t_fourstate_format.v"

test.lint(verilator_flags2=['-Wno-FUTURE'], fails=True, expect_filename=test.golden_filename)

test.extract(in_filename=test.top_filename,
             out_filename=test.root + "/docs/gen/ex_CASTFOURSTATE_faulty.rst",
             lines="13-14")

test.extract(in_filename=test.golden_filename,
             out_filename=test.root + "/docs/gen/ex_CASTFOURSTATE_msg.rst",
             lines="1-1")

test.passes()
