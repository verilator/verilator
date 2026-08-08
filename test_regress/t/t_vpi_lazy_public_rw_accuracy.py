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

test.compile(make_top_shell=False,
             make_main=False,
             verilator_flags2=[
                 "--exe --vpi --vpi-lazy-public-rw --no-l2name --stats -Wno-MULTIDRIVEN",
                 test.pli_filename
             ])

test.execute()

# 14 reconstructed (continuous assigns, aliases)
test.file_grep(test.stats, r'VPI, lazy reconstructed\s+(\d+)', 14)
# 14 comb reconstructed
test.file_grep(test.stats, r'VPI, lazy comb reconstructed\s+(\d+)', 14)
# 9 fallback retained
test.file_grep(test.stats, r'VPI, lazy fallback retained\s+(\d+)', 9)
# 3 write-only sequential
test.file_grep(test.stats, r'VPI, lazy write-only retained\s+(\d+)', 3)
# 3 ports lazy-flagged
test.file_grep(test.stats, r'VPI, lazy public rw variables\s+(\d+)', 3)
# 7 retargeted aliases
test.file_grep(test.stats, r'VPI, lazy alias retargeted\s+(\d+)', 7)

test.passes()
