#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios("vlt_all")
test.top_filename = "t/t_vpi_forceable_unpacked_struct.v"
test.pli_filename = "t/t_vpi_forceable_unpacked_struct.cpp"

test.compile(
    make_top_shell=False,
    make_pli=True,
    verilator_flags2=["--binary", "--vpi", "--vpi-lazy", "--no-l2name", test.pli_filename])

test.file_grep(test.obj_dir + "/" + test.vm_prefix + "__Syms__Slow.cpp",
               r'forceableVarInsert\("forceable_response", &\(TOP\.t__DOT__forceable_response\)')

test.execute(use_libvpi=True)

test.passes()
