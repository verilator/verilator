#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt')

test.compile(
    make_main=False,
    v_flags2=["../t/t_lib_trace.cpp", "--cc", "--trace", "--build", "--lib-create", "simulator"])

test.run(logfile=test.obj_dir + "/vlt_compile.log",
         cmd=[
             os.environ["CXX"], "-o", f"{test.obj_dir}/Vt_lib_trace", "t/t_lib_trace_caller.cpp",
             "-latomic", f"{test.obj_dir}/libsimulator.so", f"-I{test.obj_dir}",
             f"-I{os.environ['VERILATOR_ROOT']}/include"
         ])

test.execute()

test.passes()
