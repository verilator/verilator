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
test.top_filename = "t/t_lib_prot_secret.v"

# The library is named exactly as given
test.compile(verilator_flags2=["--lib-create", "lib__DOT__name"],
             verilator_make_gcc=False,
             verilator_make_gmake=False,
             make_main=False,
             make_top_shell=False)

test.file_grep(test.obj_dir + "/lib__DOT__name.sv", r'^module lib__DOT__name \(')
test.file_grep(test.obj_dir + "/lib__DOT__name.sv", r'^verilator_lib -module "lib__DOT__name"')

test.passes()
