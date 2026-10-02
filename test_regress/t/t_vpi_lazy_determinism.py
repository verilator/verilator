#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap
import glob
import os
import shutil

test.scenarios('vlt')

# Any design with enough cones to split across files will do.
test.top_filename = "t/t_vpi_scope_topology.v"
test.golden_filename = "t/t_vpi_scope_topology.out"
test.pli_filename = "t/t_vpi_dump.cpp"

verilator_flags2 = [
    "--exe --vpi --timing --vpi-lazy --no-l2name --no-skip-identical", test.pli_filename,
    "t/TestVpiMain.cpp"
]

test.clean_objs()

test.compile(make_top_shell=False,
             make_main=False,
             make_pli=True,
             verilator_flags2=verilator_flags2,
             make_flags=['CPPFLAGS_ADD=-DVL_NO_LEGACY'])
test.execute(use_libvpi=True, expect_filename=test.golden_filename)

obj_dir1 = test.obj_dir

obj_dir2 = test.obj_dir + "/obj_dir_2"
# A stale file in either obj_dir would read as a difference
shutil.rmtree(obj_dir2, ignore_errors=True)
os.makedirs(obj_dir2)

# Run 1's driver defaults, only redirected to obj_dir2
verilator_flags_run2 = [obj_dir2 if f == obj_dir1 else f for f in test.verilator_flags]
vlt_cmd2 = test.compile_vlt_cmd(verilator_flags=verilator_flags_run2,
                                verilator_flags2=verilator_flags2,
                                make_main=False)
test.run(cmd=vlt_cmd2, logfile=obj_dir2 + "/vlt_compile.log", tee=True, verilator_run=True)


def gen_files(obj_dir):
    names = (glob.glob(obj_dir + "/*.cpp") + glob.glob(obj_dir + "/*.h"))
    return sorted(os.path.basename(f) for f in names if not f.endswith("__ALL.cpp"))


files1 = gen_files(obj_dir1)
files2 = gen_files(obj_dir2)

if len(files1) < 10:
    test.error("Too few generated files to be a meaningful determinism check: " +
               str(len(files1)) + " in " + obj_dir1)
if files1 != files2:
    test.error("Generated file SETS differ between the two verilations:\n  run1: " + str(files1) +
               "\n  run2: " + str(files2))

print("%Info: t_vpi_lazy_determinism: comparing " + str(len(files1)) +
      " generated .cpp/.h files between two independent verilations of the same source")

for fname in files1:
    test.files_identical(obj_dir1 + "/" + fname, obj_dir2 + "/" + fname)

test.passes()
