#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2024 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('simulator_st')
test.top_filename = "t/t_opt_life.v"

test.compile(verilator_flags2=['--stats', '-fno-assemble'])

test.file_grep_not(test.stats, r'Optimizations, Concat merges\s+(\d+)')

test.passes()
