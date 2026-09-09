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
test.top_filename = "t/t_ins_dpi_hook.v"

# The trigger step of a hook must be positive
test.compile(fails=True,
             make_main=False,
             verilator_make_gmake=False,
             v_flags2=["--dpihook-trigger-step 0"],
             expect_filename=test.golden_filename)

test.passes()
