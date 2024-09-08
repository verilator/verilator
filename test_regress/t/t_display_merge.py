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

test.execute(expect_filename=test.golden_filename)

test.file_grep(test.obj_dir + "/" + test.vm_prefix + "__stats.txt",
               r'Node count, DISPLAY \s+ 44 \s+ 27 \s+ 27 \s+ 6')

test.passes()
