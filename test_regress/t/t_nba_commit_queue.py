#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt_all')

test.compile(verilator_flags2=["-unroll-count 1", "--stats"])

test.execute()

test.file_grep(test.stats, r'NBA, variables using ValueQueueWhole scheme\s+(\d+)', 6)
test.file_grep(test.stats, r'NBA, variables using ValueQueuePartial scheme\s+(\d+)', 3)

test.passes()
