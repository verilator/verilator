#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt')
test.top_filename = "t/t_protect_ids.v"

test.compile(verilator_flags2=["--protect-ids --protect-key SECRET_KEY", "t/t_protect_ids_c.cpp"])

test.execute()

# Since using a named key, we can check for always identical maptest.files_identical(test.obj_dir + "/"+test.vm_prefix+"__idmap.xml", test.golden_filename)

test.passes()
