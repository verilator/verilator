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

test.compile(verilator_flags2=['--coverage'])

test.execute()

# Check that coverage database contains functional coverage entries
# Format uses control characters as delimiters: C '^At^Bfunccov^Apage...bin^Blow...h^Bcg.cp.low' count
test.file_grep(test.coverage_filename, r'funccov')
test.file_grep(test.coverage_filename, r'bin.{0,2}low')  # binlow with possible delimiter
test.file_grep(test.coverage_filename, r'bin.{0,2}high')  # binhigh with possible delimiter
test.file_grep(test.coverage_filename, r'cg\.cp\.low')
test.file_grep(test.coverage_filename, r'cg\.cp\.high')

# Verify both bins have non-zero counts (they were both sampled)
test.file_grep(test.coverage_filename, r'.*bin.{0,2}low.*\' [1-9]')
test.file_grep(test.coverage_filename, r'.*bin.{0,2}high.*\' [1-9]')

test.passes()
