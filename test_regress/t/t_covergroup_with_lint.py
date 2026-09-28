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
test.top_filename = 't/t_covergroup_with.v'

test.lint(verilator_flags2=['-Wwarn-UNUSEDSIGNAL', '-Wwarn-VARHIDDEN', '-Wno-fatal'])

# A 'with' filter may read all, some, or none of the bits of its implicit candidate 'item'
test.file_grep_not(test.compile_log_filename, r"_item'")
# The candidate hides another 'item' in the filter without a warning, unlike the declarations
# the test names 'item', of the members and arguments of classes and covergroups
test.file_grep_count(test.compile_log_filename, r"hides declaration in upper scope: 'item'", 4)

test.passes()
