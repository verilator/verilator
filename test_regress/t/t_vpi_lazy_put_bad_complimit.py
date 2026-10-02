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
test.top_filename = "t/t_vpi_lazy_put_bad.v"
test.pli_filename = "t/t_vpi_lazy_put_bad.cpp"
test.golden_filename = "t/t_vpi_lazy_put_bad.out"

# The temp shadows of a cone V3DepthBlock splits must stay visible to its sub-funcs
test.compile(make_top_shell=False,
             make_main=False,
             verilator_flags2=[
                 "--exe --vpi --vpi-lazy --no-l2name --comp-limit-blocks 3 -fno-inline-cfuncs",
                 test.pli_filename
             ])

test.file_grep_any(test.glob_some(test.obj_dir + "/" + test.vm_prefix + "*.cpp"),
                   r'void \S+__Vlazy_reconstruct__\d+__deep\d+\(')

test.execute(expect_filename=test.golden_filename)

test.passes()
