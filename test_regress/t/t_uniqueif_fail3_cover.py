#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('simulator')
test.top_filename = "t/t_uniqueif.v"

# Coverage adds an else counter to the final if, which must not count as an else
test.compile(v_flags2=['+define+FAILING_ASSERTION3'],
             verilator_flags2=['--assert', '--coverage'],
             nc_flags2=['+assert'],
             fails=test.nc)

test.execute(fails=test.vlt_all, expect_filename="t/t_uniqueif_fail3.out")

test.passes()
