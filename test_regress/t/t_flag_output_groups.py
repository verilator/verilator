#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2024 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt_all')

# Split output so there are enough files to group
test.compile(verilator_flags2=["--output-groups", "2", "--output-split", "1"])

test.execute()

# Check that only vm_classes_*.cpp are to be compiled
test.file_grep(test.obj_dir + "/" + test.vm_prefix + "_classes.mk", "vm_classes_1")
test.file_grep_not(test.obj_dir + "/" + test.vm_prefix + "_classes.mk", "vm_classes_2")

test.passes()
