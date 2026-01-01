#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2025 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt_all')

lib_dir = test.obj_dir + "/sub"
test.mkdir_ok(lib_dir)

test.run(logfile=lib_dir + "/verilator.log",
         cmd=[
             "perl", os.environ["VERILATOR_ROOT"] + "/bin/verilator", "-cc", "-Mdir", lib_dir,
             "--lib-create", "sub", "--prefix", "Vsub", "+define+LIB_CREATE", test.top_filename
         ],
         verilator_run=True)

test.run(logfile=lib_dir + "/make.log", cmd=[os.environ["MAKE"], "-C", lib_dir, "-f", "Vsub.mk"])

test.compile(verilator_flags2=["--binary", "-LDFLAGS", "sub/libsub.a", lib_dir + "/sub.sv"])

test.execute(xsim_run_flags2=["--sv_lib", lib_dir + "/libsecret", "--dpi_absolute"])

test.passes()
