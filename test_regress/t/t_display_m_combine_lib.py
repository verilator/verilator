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

lib_dir = test.obj_dir + "/lib"
test.mkdir_ok(lib_dir)

test.run(logfile=lib_dir + "/verilator.log",
         cmd=[
             "perl", os.environ["VERILATOR_ROOT"] + "/bin/verilator", "-cc", "-Mdir", lib_dir,
             "--lib-create", "lib", "--prefix", "Vlib", "--top-module", "lib", "--stats",
             test.top_filename
         ],
         verilator_run=True)

test.run(logfile=lib_dir + "/make.log", cmd=[os.environ["MAKE"], "-C", lib_dir, "-f", "Vlib.mk"])

test.file_grep(lib_dir + "/Vlib__stats.txt", r'Optimizations, Combined CFuncs\s+(\d+)', 2)

test.compile(verilator_flags2=[
    "--binary", "-LDFLAGS", "lib/liblib.a", "+define+USE_LIB", lib_dir + "/lib.sv"
])

test.execute(check_finished=False)

# Order of lines is unspecified, so don't use a golden file
for inst in ("u0", "u1", "u2"):
    for suffix in ("", ".blk", ".tsk"):
        test.file_grep(test.run_log_filename, r"In 't.u_lib." + inst + suffix + "'")

test.passes()
