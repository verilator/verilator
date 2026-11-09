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
test.top_filename = "t/t_EXAMPLE.v"

test.lint(v_flags=["--debugi 3 --verilate-jobs 2 --debug-self-test --debug-fatalsrc-worker"],
          fails='any')
test.file_grep(test.compile_log_filename,
               r'%Error: Internal Error: .*: --debug-fatalsrc-worker')
test.file_grep(test.compile_log_filename, r'Aborting since under --debug')
test.file_grep_not(test.compile_log_filename, r'Resource deadlock avoided|std::system_error')

test.passes()
