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

test.compile()

test.execute()

test.files_identical(test.obj_dir + "/t_sys_writemem_c_b.mem", "t/t_sys_readmem_assoc_c_b.out")
test.files_identical(test.obj_dir + "/t_sys_writemem_w_h.mem", "t/t_sys_readmem_assoc_w_h.out")

test.passes()
