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
test.top_filename = "t/t_vpi_lazy_public_rw_foldcorners.v"

# --vpi-lazy-fold-budget 0 disables fold/assembly; all targets retained.
test.compile(verilator_flags2=[
    "--vpi --vpi-lazy-public-rw --vpi-lazy-fold-budget 0 --stats"
    " -Wno-MULTIDRIVEN -Wno-UNOPTFLAT -Wno-WIDTHTRUNC -Wno-WIDTHEXPAND"
    " -Wno-UNUSEDSIGNAL -Wno-BLKANDNBLK -Wno-ALWCOMBORDER"
])

test.file_grep(test.stats, r'VPI, lazy comb reconstructed\s+(\d+)', 0)
test.file_grep(test.stats, r'VPI, lazy fallback retained\s+([1-9]\d*)')

test.passes()
