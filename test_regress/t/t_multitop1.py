#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt_all')

test.compile()

test.execute(check_finished=False)

# Order of lines is unspecified, so don't use a golden file
test.file_grep(test.run_log_filename, r"In 'top.t'")
test.file_grep(test.run_log_filename, r"In 'top.t.s'")
test.file_grep_not(test.run_log_filename, r"in_subfile")

test.passes()
