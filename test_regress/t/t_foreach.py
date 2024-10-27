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

test.compile(verilator_flags2=['--assert'])

test.execute()

# We expect all loops should be unrolled by verilator,
# none of the loop variables should exist in the output:
for filename in test.glob_some(test.obj_dir + "/" + test.vm_prefix + "*.cpp"):
    test.file_grep_not(filename, r'index_')

# Further, we expect that all logic within the loop should
# have been evaluated inside the compiler. So there should be
# no references to 'sum' in the .cpp.
for filename in test.glob_some(test.obj_dir + "/" + test.vm_prefix + "*.cpp"):
    test.file_grep_not(filename, r'[^a-zA-Z]sum[^a-zA-Z]')

test.passes()
