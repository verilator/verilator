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

# -Wno-UNOPTFLAT: seedv read/written in same statement; -Wno-WIDTHTRUNC: $random as bit index.
test.compile(make_top_shell=False,
             make_main=False,
             verilator_flags2=[
                 "--exe --vpi --vpi-lazy-public-rw --no-l2name"
                 " -Wno-UNOPTFLAT -Wno-WIDTHTRUNC", test.pli_filename
             ])

test.execute()

test.passes()
