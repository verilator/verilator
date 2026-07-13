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

# --vpi-lazy-public-rw + --protect-ids: VPI names obfuscated; compile+run.
# -Wno-INSECURE: --protect-ids + --vpi intentional.
test.compile(make_top_shell=False,
             make_main=False,
             verilator_flags2=[
                 "--exe --vpi --vpi-lazy-public-rw --protect-ids"
                 " --protect-key SECRET_KEY --no-l2name --stats -Wno-INSECURE", test.pli_filename
             ])

test.execute()

test.file_grep(test.stats, r'VPI, lazy reconstructed\s+(\d+)', 1)
test.file_grep(test.stats, r'VPI, lazy alias retargeted\s+(\d+)', 4)

test.passes()
