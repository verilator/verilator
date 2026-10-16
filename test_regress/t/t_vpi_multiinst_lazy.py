#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt_all')
test.top_filename = "t/t_vpi_multiinst.v"
test.golden_filename = "t/t_vpi_multiinst.out"
test.pli_filename = "t/t_vpi_dump.cpp"

# No --vpi: the lazy tables are reachable only through VPI, so --vpi-lazy alone must build a VPI
# model rather than self-disabling. Under vltmt, reads from the thread that calls eval() behave
# as they do single-threaded.
test.compile(make_top_shell=False,
             make_main=False,
             make_pli=True,
             verilator_flags2=[
                 "--exe --timing --vpi-lazy --no-l2name --stats", test.pli_filename,
                 "t/TestVpiMain.cpp"
             ],
             make_flags=['CPPFLAGS_ADD=-DVL_NO_LEGACY'])

test.execute(use_libvpi=True, expect_filename=test.golden_filename)

# Interface members t drives per instance, ports read from the parent, and a cone in their own
# shared scope that reads them are anchored in the top scope; if1.l and if1.s keep their storage
# apart from if0's reconstructed instances
test.file_grep(test.stats, r'VPI, lazy reconstructed\s+(\d+)', 71)

test.passes()
