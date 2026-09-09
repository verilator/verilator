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

dpi_filename = "t/t_ins_dpi_hook_dpi.cpp"
vlt_filename = "t/" + test.name + ".vlt"

# insert_dpihook adds an override driver on the hooked nets, which is expected
# to look like a second combinational driver / circular comb logic.
test.compile(make_main=False,
             v_flags2=[
                 "--trace --timing --exe -Wno-MULTIDRIVEN -Wno-UNOPTFLAT", vlt_filename,
                 dpi_filename, test.pli_filename
             ])

test.execute(expect_filename=test.golden_filename)

test.passes()
