#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap
import coverage_covergroup_common

test.scenarios('vlt')

# WITH --coverage, which is the point: it turns off the free path in
# VlCovergroupType::retire().  The golden report is the other half -- both
# instances' bins must survive the design dropping both handles.
#
# Also AddressSanitizer, rather than a separate _asan variant: this is the only
# retain-path test, and a wrong free there is a use-after-free the golden
# report would catch only if freed storage read back as a wrong number.  Not
# --runtime-debug: its extra checks add nothing here and triple the runtime
# recompile.  ASAN is incompatible with TSAN, which --runtime-debug would have
# made driver.py notice for us.
if test.tsan:
    test.skip("ThreadSanitizer not compatible with AddressSanitizer\n")

coverage_covergroup_common.run(test,
                               verilator_flags2=[
                                   "-CFLAGS -fsanitize=address -CFLAGS -ggdb"
                                   " -LDFLAGS -fsanitize=address -LDFLAGS -ggdb"
                               ])
