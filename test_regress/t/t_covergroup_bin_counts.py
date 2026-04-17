#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap
import coverage_covergroup_common

test.scenarios('vlt')

test.compile(verilator_flags2=['--coverage'])

test.execute()

coverage_covergroup_common.covergroup_coverage_report(test)
test.files_identical(test.obj_dir + '/covergroup_report.txt', test.golden_filename)

# Verify coverage.dat format contains covergroup entries (replaces t_covergroup_database)
test.file_grep(test.coverage_filename, r'covergroup')
test.file_grep(test.coverage_filename, r'bin.{0,2}low')
test.file_grep(test.coverage_filename, r'bin.{0,2}high')
test.file_grep(test.coverage_filename, r'cg_db\.cp\.low')
test.file_grep(test.coverage_filename, r'cg_db\.cp\.high')
test.file_grep(test.coverage_filename, r'.*bin.{0,2}low.*\' [1-9]')
test.file_grep(test.coverage_filename, r'.*bin.{0,2}high.*\' [1-9]')

test.passes()
