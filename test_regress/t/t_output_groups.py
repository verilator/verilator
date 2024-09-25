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

test.compile(verilator_flags2=["--no-skip-identical", "--output-groups", "2"])

test.execute()

# Check that only vm_classes_*.cpp were compiled
test.file_grep_not(test.obj_dir + "/vlt_gcc.log", "Foo")
test.file_grep(test.obj_dir + "/vlt_gcc.log", "vm_classes_slow_1.cpp")
test.file_grep(test.obj_dir + "/vlt_gcc.log", "vm_classes_fast_1.cpp")
test.file_grep_not(test.obj_dir + "/vlt_gcc.log", "vm_classes_slow_2.cpp")
test.file_grep_not(test.obj_dir + "/vlt_gcc.log", "vm_classes_fast_2.cpp")

test.passes()
