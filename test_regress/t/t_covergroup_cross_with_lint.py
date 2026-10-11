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
test.top_filename = 't/t_covergroup_cross_with.v'

test.lint(verilator_flags2=['-Wwarn-UNUSEDSIGNAL', '-Wwarn-VARHIDDEN', '-Wno-fatal'])

# A filter's cross items, which the standard names, hide others without a warning, and a filter
# may read all, some, or none of them
test.file_grep_not(test.compile_log_filename, r"hides declaration in upper scope: '[ab]'")
test.file_grep_not(test.compile_log_filename, r"not used: '(a|b|aa|bb|ee|nn|pp|ss|ww|xp|yp)'")

test.passes()
