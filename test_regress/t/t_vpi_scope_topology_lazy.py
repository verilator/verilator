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

test.scenarios('vlt_all')
test.top_filename = "t/t_vpi_scope_topology.v"
test.golden_filename = "t/t_vpi_scope_topology.out"
test.pli_filename = "t/t_vpi_dump.cpp"

flags = [
    "--exe --vpi --timing --vpi-lazy --no-l2name --stats", test.pli_filename, "t/TestVpiMain.cpp"
]

# A stale file in obj_dir would read as a nondeterministic one
test.clean_objs()
test.compile(make_top_shell=False,
             make_main=False,
             make_pli=True,
             verilator_flags2=flags,
             make_flags=['CPPFLAGS_ADD=-DVL_NO_LEGACY'])

test.execute(use_libvpi=True, expect_filename=test.golden_filename)

test.file_grep(test.stats, r'VPI, lazy reconstructed\s+(\d+)', 120)
# Every u_pull*.pi, read from t's scope: pull_x is stored, feeding two of them
test.file_grep(test.stats, r'VPI, lazy cross-scope copy descriptors\s+(\d+)', 3)
# hs_v's kept store counts as a use, so V3Gate does not also inline it into hs_q; nor pull_x
# into its two readers
test.file_grep(test.stats, r'Gate signals not inlined due to cost\s+(\d+)', 3)
# u_cat's output temp is read through a helper shadow, not pinned storage; nor are the decomposed
# bytes of intf.wdata/swapped, written from other scopes, whose cones intf's scope anchors
test.file_grep(test.stats, r'VPI, lazy boundary storage pinned\s+(\d+)', 1)

# A second verilation of the same source must generate identical files
obj_dir2 = test.obj_dir + "/obj_dir_2"
shutil.rmtree(obj_dir2, ignore_errors=True)
os.makedirs(obj_dir2)
vlt_cmd2 = test.compile_vlt_cmd(
    verilator_flags=[obj_dir2 if f == test.obj_dir else f for f in test.verilator_flags],
    verilator_flags2=flags,
    make_main=False)
test.run(cmd=vlt_cmd2, logfile=obj_dir2 + "/vlt_compile.log", tee=True, verilator_run=True)


def gen_files(obj_dir):
    names = glob.glob(obj_dir + "/*.cpp") + glob.glob(obj_dir + "/*.h")
    return sorted(os.path.basename(f) for f in names if not f.endswith("__ALL.cpp"))


files1 = gen_files(test.obj_dir)
if files1 != gen_files(obj_dir2):
    test.error("Generated file sets differ between two verilations")
for fname in files1:
    test.files_identical(test.obj_dir + "/" + fname, obj_dir2 + "/" + fname)

test.passes()
