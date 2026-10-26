#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('simulator')

test.compile()

test.execute()

test.file_grep(test.obj_dir + "/writemem_dyn_d.hex", r'^02\n01\n$')
test.file_grep(test.obj_dir + "/writemem_dyn_a.hex", r'^01\n02\n$')
test.file_grep(test.obj_dir + "/writemem_dyn_empty.hex", r'^$')

test.passes()
