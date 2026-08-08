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

# -Wno-MULTIDRIVEN: 'w' is deliberately multidriven.
test.compile(make_top_shell=False,
             make_main=False,
             verilator_flags2=[
                 "--exe --vpi --vpi-lazy-public-rw --stats -Wno-MULTIDRIVEN", test.pli_filename
             ])

test.execute()

syms = test.obj_dir + "/" + test.vm_prefix + "__Syms__Slow.cpp"

test.file_grep(test.stats, r'VPI, lazy fallback retained\s+(\d+)', 1)
test.file_grep(syms, r'"w",.*VLVF_PUB_RW')

test.file_grep(test.stats, r'VPI, lazy reconstructed\s+(\d+)', 1)
test.file_grep(syms, r'__Vlazyrecon__t__DOT__r.*VLVF_CONTINUOUSLY')

test.passes()
