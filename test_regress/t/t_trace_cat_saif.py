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

test.compile(make_top_shell=False,
             make_main=False,
             v_flags2=["--trace-saif --exe", test.pli_filename])

test.execute()

test.saif_identical(test.obj_dir + "/simpart_0000.fst", "t/" + test.name + "_0000.out")
test.saif_identical(test.obj_dir + "/simpart_0100.fst", "t/" + test.name + "_0100.out")

test.passes()
