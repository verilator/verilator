#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt')

test.compile(verilator_flags2=['--stats'])

test.file_grep(test.stats, r'Optimizations, Gate excluded wide expressions\s+(\d+)', 1)
test.file_grep(test.stats, r'Optimizations, Substituted temps\s+(\d+)', 642)

test.passes()
