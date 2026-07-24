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

test.compile(
    make_top_shell=False,
    make_main=False,
    verilator_flags2=["--exe --vpi --vpi-lazy-public-rw --no-l2name --stats", test.pli_filename])

test.execute()

# Same-scope driver (child.cy) reconstructs; cross-scope driver (parent.py,
# which reads into its child instance) retains instead. Two instances each.
test.file_grep(test.stats, r'VPI, lazy reconstructed\s+(\d+)', 2)
test.file_grep(test.stats, r'VPI, lazy reconstructed members\s+(\d+)', 1)
test.file_grep(test.stats, r'VPI, lazy cross-scope retained\s+(\d+)', 2)

test.passes()
