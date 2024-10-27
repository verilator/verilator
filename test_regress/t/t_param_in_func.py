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

test.compile(verilator_flags2=["--stats"])

test.execute()

# The parameter array should have been put in the constant pool
if test.vlt_all:
    test.file_grep(test.stats, r'ConstPool, Tables emitted\s+(\d+)', 3)

# Shouldn't have any references to the parameter array
for filename in (test.glob_some(test.obj_dir + "/" + test.vm_prefix + "*.h") +
                 test.glob_some(test.obj_dir + "/" + test.vm_prefix + "*.cpp")):
    test.file_grep_not(filename, r'digits')

test.passes()
