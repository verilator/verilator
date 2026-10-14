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
test.top_filename = "t/t_lib_prot_inout.v"

# Keep the lowered ports exposed, and dump their library inout attributes.
test.compile(verilator_flags2=[
    "--protect-lib", "secret", "--protect-key", "secret-key", "--pins-inout-enables",
    "--dumpi-tree", "3"
],
             verilator_make_gmake=False,
             make_main=False)

wrapper = test.obj_dir + "/secret.sv"
test.file_grep(wrapper, r'input logic z_secret\b')
test.file_grep(wrapper, r'output logic z_secret__out\b')
test.file_grep(wrapper, r'output logic z_secret__en\b')
test.file_grep_not(wrapper, r'inout\s')

tree = test.glob_one(test.obj_dir + "/*_tristate.tree")
test.file_grep(tree, r'libInoutId=[1-9][0-9]*')
test.file_grep(tree, r'\[LIBINOUTEN\]')

test.passes()
