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

test.unlink_ok(test.obj_dir + "/t_sys_file_basic_test.log")

test.compile(
    # Build without cached objects, see bug363
    make_flags=['VM_PARALLEL_BUILDS=0'])

test.execute()
test.files_identical(test.obj_dir + "/t_sys_file_basic_test.log", test.golden_filename)

test.passes()
