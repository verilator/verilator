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
test.top_filename = "t/t_vpi_onetime_cbs.v"
test.pli_filename = "t/t_vpi_onetime_cbs.cpp"

test.compile(make_top_shell=False,
             make_pli=True,
             verilator_flags2=["--binary --vpi --vpi-lazy", test.pli_filename],
             v_flags2=["+define+USE_VPI_NOT_DPI"])

test.execute(check_finished=True, use_libvpi=True)

test.passes()
