#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3,
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('simulator')
test.top_filename = "t/t_cover_genfor.v"

test.compile(verilator_flags2=[
    '--binary', '--coverage-line', '--coverage-branch', '--coverage-user',
    '--coverage-per-instance', '--protect-ids', '--protect-key SECRET_KEY'
])

test.execute(all_run_flags=[" +verilator+coverage+file+" + test.obj_dir + "/coverage.dat"])

# Block names are protected in the coverage hierarchy
test.file_grep_not(test.obj_dir + "/coverage.dat", r'g_loop|g_nest|g_decl|b_named|g_cover|genblk')
# User covers and line/branch points protect a block under the same name
idmap = test.obj_dir + "/" + test.vm_prefix + "__idmap.xml"
test.file_grep(idmap, r'to="g_cover\[0\]"')
test.file_grep(idmap, r'to="b_named"')
test.file_grep_not(idmap, r'to="g_cover__BRA__|to="b_named__DOT__unnamedblk')

test.passes()
