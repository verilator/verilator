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

test.compile(verilator_flags2=["--stats", test.wno_unopthreads_for_few_cores])

test.execute()

#Optimization is disabled
#test.file_grep(test.stats, r'Optimizations, Gaters inserted\s+(\d+)'i, 3)

test.passes()
