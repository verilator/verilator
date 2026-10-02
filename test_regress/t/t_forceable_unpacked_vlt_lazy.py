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
test.pli_filename = "t/t_forceable_unpacked.cpp"
test.top_filename = "t/t_forceable_unpacked.v"

test.compile(make_top_shell=False,
             make_main=False,
             verilator_flags2=[
                 '--exe', test.pli_filename, test.t_dir + "/t_forceable_unpacked.vlt", '--vpi',
                 '--vpi-lazy'
             ])

test.file_grep(test.obj_dir + "/" + test.vm_prefix + "__Syms__Slow.cpp",
               r'forceableVarInsert\("var_arr", &\(TOP\.t__DOT__var_arr\)')

test.execute()

test.passes()
