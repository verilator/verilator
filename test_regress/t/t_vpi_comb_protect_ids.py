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

test.top_filename = "t/t_vpi_comb_trace.v"

test.compile(make_top_shell=False,
             make_pli=True,
             verilator_flags2=[
                 "--binary --vpi --public-flat-rw --protect-ids --no-l2name -Wno-INSECURE"
                 " +define+NO_T_VPI_DUMP", test.pli_filename
             ])

test.execute(use_libvpi=True, check_finished=True)

test.passes()
