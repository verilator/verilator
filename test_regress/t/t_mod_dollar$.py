#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt')

# This doesn't use the general compile rule as we want to make sure we form
# prefix properly using post-escaped identifiers
test.run(cmd=[
    os.environ["VERILATOR_ROOT"] + "/bin/verilator",
    "--cc",
    "--Mdir " + test.obj_dir + "/t_mod_dollar",
    "--exe --build --main",
    't/t_mod_dollar$.v',
],
         verilator_run=True)

test.passes()
