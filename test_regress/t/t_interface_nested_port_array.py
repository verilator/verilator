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

# Reject unsupported indexed interface forwarding without an internal error (issue #5066).
test.lint(fails=True)
test.file_grep(test.compile_log_filename, r"Illegal port connection 'l0'")
test.file_grep_not(test.compile_log_filename, r"Internal Error")

test.passes()
