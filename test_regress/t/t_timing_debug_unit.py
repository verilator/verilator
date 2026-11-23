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

test.compile(verilator_flags2=["--binary", "--runtime-debug"])

test.execute(all_run_flags=["+verilator+debug"])

# The compilation-unit package, also before a class in it, is written as is, while other escaped
# packages and user identifiers named '$unit' are escaped
test.file_grep(test.run_log_filename, r'waiting for @\(\[event\] \$unit\.unit_ev\)')
test.file_grep(test.run_log_filename, r'waiting for @\(\[event\] \$unit::UCls')
test.file_grep(test.run_log_filename, r'waiting for @\(\[event\] \\pkg\.esc \.ev\)')
test.file_grep(test.run_log_filename, r'waiting for @\(posedge t\.\\\$unit \)')
test.file_grep(test.run_log_filename, r'waiting for @\(\[event\] t\.g\.\\\$unit \.ev\)')

test.passes()
