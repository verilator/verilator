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

if not test.have_solver:
    test.skip("No constraint solver installed")

test.compile(
    # Ensure we test captures of static variables
    verilator_flags2=["--fno-inline"])

test.execute()

for filename in test.glob_some(test.obj_dir + "/" + test.vm_prefix + "*Baz*.cpp"):
    # Check that "Baz" has no constrained random generator
    test.file_grep_not(filename, "this->__PVT__constraint")

test.passes()
