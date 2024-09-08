#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap
import sys

test.scenarios('vlt')

CXX = os.environ["CXX"]

test.run(
    cmd=[
        "cd " + test.obj_dir  #
        + " && " + CXX + " -c ../../t/t_flag_ldflags_a.cpp"  #
        + " && ar -cr t_flag_ldflags_a.a t_flag_ldflags_a.o"  #
        + " && ranlib t_flag_ldflags_a.a "
    ],
    check_finished=False)

test.run(
    cmd=[
        "cd " + test.obj_dir  #
        + " && " + CXX + " -fPIC -c ../../t/t_flag_ldflags_so.cpp"  #
        + " && " + CXX + " -shared -o t_flag_ldflags_so.so -lc t_flag_ldflags_so.o"
    ],
    check_finished=False)

test.compile(
    # Pass multiple -D's so we check quoting works properly
    v_flags2=[
        "-CFLAGS '-DCFLAGS_FROM_CMDLINE -DCFLAGS2_FROM_CMDLINE' ", "t/t_flag_ldflags_c.cpp",
        "t_flag_ldflags_a.a", "t_flag_ldflags_so.so"
    ])

# On OS X, LD_LIBRARY_PATH is ignored, so set rpath of the exe to find the .so
if sys.platform == "darwin":
    test.run(cmd=[
        "cd " + test.obj_dir + " && install_name_tool -add_rpath @executable_path/.",
        test.vm_prefix
    ],
             check_finished=False)

    test.run(cmd=[
        "cd " + test.obj_dir + " && install_name_tool -change t_flag_ldflags_so.so" +
        " @rpath/t_flag_ldflags_so.so", test.vm_prefix
    ],
             check_finished=False)

test.execute(run_env="LD_LIBRARY_PATH=" + test.obj_dir + ":" +
             test.getenv_def("LD_LIBRARY_PATH", ""))

test.passes()
