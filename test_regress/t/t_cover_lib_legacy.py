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
test.top_filename = "t/t_cover_lib.v"

test.compile(v_flags2=["--coverage t/t_cover_lib_c.cpp"],
             verilator_flags2=["--exe -Wall -Wno-DECLFILENAME"],
             make_flags=['CPPFLAGS_ADD=-DTEST_OBJ_DIR="' + test.obj_dir + '"'],
             make_top_shell=False,
             make_main=False)

test.execute()
test.files_identical_sorted(test.obj_dir + "/coverage1.dat", "t/t_cover_lib__1.out")
test.files_identical_sorted(test.obj_dir + "/coverage2.dat", "t/t_cover_lib__2.out")
test.files_identical_sorted(test.obj_dir + "/coverage3.dat", "t/t_cover_lib__3.out")
test.files_identical_sorted(test.obj_dir + "/coverage4.dat", "t/t_cover_lib__4.out")

test.passes()
