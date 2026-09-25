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
test.top_filename = "t/t_iface_typedef_bits_uaf.v"

test.lint(
    # Check we can dump the interface capture ledger
    v_flags=["--debug --debugi 0 --debugi-V3LinkDotIfaceCapture 9"])

test.file_grep(test.compile_log_filename, r'iface capture dumpEntries: after finalizeIfaceCapture')

test.passes()
