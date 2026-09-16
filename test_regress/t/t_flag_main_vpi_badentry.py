#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2025 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt')
test.fourstate_capable = False

# A valid library loaded with a :<bootstrap> entry that does not exist must
# fail with a clear error (the missing-named-bootstrap branch of the loader).
test.top_filename = 't/t_flag_main_vpi.v'
test.pli_filename = 't/t_flag_main_vpi.cpp'

test.compile(make_pli=True, verilator_flags2=["--binary --vpi --public-flat-rw"])

test.execute(fails=True,
             all_run_flags=["+verilator+vpi+" + test.obj_dir + "/libvpi.so:no_such_fn"],
             expect_filename=test.golden_filename)

test.passes()
