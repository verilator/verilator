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

# +verilator+vpi+ pointing at a non-existent library must fail with a clear
# error (the dlopen-failure branch of the runtime loader).
test.top_filename = 't/t_flag_main_vpi.v'

test.compile(verilator_flags2=["--binary --vpi --public-flat-rw"])

# The fatal names the (stable, relative) library path; the platform-specific dlerror()
# detail is emitted on a "- " line, which golden comparison strips, so the .out is portable.
test.execute(fails=True,
             all_run_flags=["+verilator+vpi+" + test.obj_dir + "/nonexistent.so"],
             expect_filename=test.golden_filename)

test.passes()
