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

if not test.have_solver:
    test.skip("No constraint solver installed")

# --debug-check's structural check fires on the dropped index before the
# gate under test runs, so opt out to check the gate's own diagnostic
test.lint(verilator_flags2=["--no-debug-check"],
          fails=True,
          expect_filename=test.golden_filename)

test.passes()
