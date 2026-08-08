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
                 "--exe --vpi --vpi-lazy-public-rw --trace --no-l2name --stats", test.pli_filename
             ])

test.execute()

test.file_grep(test.stats, r'VPI, lazy reconstructed\s+(\d+)', 1)
test.file_grep(test.stats, r'VPI, lazy alias retargeted\s+(\d+)', 4)

if not os.path.exists(test.trace_filename):
    test.error("VCD file was not created: " + test.trace_filename)
elif os.stat(test.trace_filename).st_size == 0:
    test.error("VCD file is empty: " + test.trace_filename)
else:
    test.file_grep(test.trace_filename, r'\$var')
    test.file_grep(test.trace_filename, r'keep')

test.passes()
