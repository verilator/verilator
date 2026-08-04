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

if not test.have_solver:
    test.skip("No constraint solver installed")

test.compile()

# Constraint indices above 9 were parsed digit-by-digit from the core reply
test.execute()

test.file_grep(test.run_log_filename, r"a > 8'd200")
test.file_grep(test.run_log_filename, r"a < 8'd100")
test.file_grep(test.run_log_filename, r'All Finished')

test.passes()
