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

test.run(logfile=test.obj_dir + "/vlt_compile.log",
         cmd=[
             "perl", os.environ["VERILATOR_ROOT"] + "/bin/verilator", "-cc", "--build",
             '--no-timing', "-Mdir", test.obj_dir, "t/t_flag_lib_dpi.v",
             test.t_dir + "/t_flag_lib_dpi.cpp", test.t_dir + "/t_flag_lib_dpi_main.cpp"
         ],
         verilator_run=True)

test.run(
    logfile=test.obj_dir + "/cxx_compile.log",
    cmd=[
        "cd " + test.obj_dir  #
        + " && cp " + test.t_dir + "/t_flag_lib_dpi.mk t_flag_lib_dpi.mk"  #
        + " && " + os.environ["MAKE"] + " -f t_flag_lib_dpi.mk t_flag_lib_dpi_test"  #
        + " && ./t_flag_lib_dpi_test"
    ])

test.passes()
