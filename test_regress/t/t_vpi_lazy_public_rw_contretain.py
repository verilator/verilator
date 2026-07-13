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

# -Wno-UNUSED: 'rnd'/'base' are written but unread; -Wno-WIDTHTRUNC: $random is
# 32-bit and 'rnd' truncation is deliberate.
test.compile(make_top_shell=False,
             make_main=False,
             verilator_flags2=[
                 "--exe --vpi --vpi-lazy-public-rw --stats -Wno-UNUSED -Wno-WIDTHTRUNC",
                 test.pli_filename
             ])

test.execute()

syms = test.obj_dir + "/" + test.vm_prefix + "__Syms__Slow.cpp"

# Neither reconstructed (both retained).
test.file_grep(test.stats, r'VPI, lazy reconstructed\s+(\d+)', 0)
test.file_grep(test.stats, r'VPI, lazy comb reconstructed\s+(\d+)', 0)
# Both have real read-write entries.
test.file_grep(syms, r'"rnd",.*VLVF_PUB_RW')
test.file_grep(syms, r'"base",.*VLVF_PUB_RW')

test.passes()
