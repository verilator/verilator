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

test.scenarios('vlt')

# Determinism: two independent verilations produce byte-identical sources
verilator_flags2 = [
    "--exe --vpi --vpi-lazy-public-rw --no-l2name --no-skip-identical -Wno-UNOPTFLAT",
    test.pli_filename
]

# Run 1
test.compile(make_top_shell=False, make_main=False, verilator_flags2=verilator_flags2)
test.execute()

obj_dir1 = test.obj_dir

# Run 2: separate Mdir with same basename
obj_dir2 = os.path.dirname(obj_dir1) + "_determinism_run2/" + os.path.basename(obj_dir1)
os.makedirs(obj_dir2, exist_ok=True)

verilator_flags_run2 = [
    "-cc", "-Mdir", obj_dir2, "--fdedup", "--debug-check", "--comp-limit-members", "10"
]
vlt_cmd2 = test.compile_vlt_cmd(verilator_flags=verilator_flags_run2,
                                verilator_flags2=verilator_flags2,
                                make_main=False)
test.run(cmd=vlt_cmd2, logfile=obj_dir2 + "/vlt_compile.log", tee=True, verilator_run=True)


# Compare .cpp/.h (exclude __ALL.cpp)
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

print("%Info: t_vpi_lazy_public_rw_determinism: comparing " + str(len(files1)) +
      " generated .cpp/.h files between two independent verilations of the same source")

for fname in files1:
    test.files_identical(obj_dir1 + "/" + fname, obj_dir2 + "/" + fname)

test.passes()
