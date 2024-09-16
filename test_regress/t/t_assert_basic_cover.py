#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('simulator')
test.top_filename = "t/t_assert_basic.v"

test.compile(verilator_flags2=['--assert --cc --coverage-user'])

test.execute()

#Needs work
print("-Info:  NOT checking for coverage")
#test.file_grep(test.coverage_filename, r't=>'psl_cover',o=>'cover',c=>2\);')
#test.file_grep(test.coverage_filename, r'DefaultClock.*,c=>1\);')
#test.file_grep(test.coverage_filename, r'ToggleLogIf.*,c=>9\);')

test.passes()
