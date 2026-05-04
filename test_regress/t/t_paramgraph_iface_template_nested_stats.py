#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

# Stats-variant of t_paramgraph_iface_template_nested: verifies IfaceCapture
# statistics for deeply nested interface typedef chains with clone propagation.

import vltest_bootstrap

test.scenarios('vlt')

test.top_filename = "t/t_paramgraph_iface_template_nested.v"

test.compile(v_flags2=["--binary --stats"])

test.file_grep(test.stats, r'IfaceCapture, Entries total\s+(\d+)', 25)
test.file_grep(test.stats, r'IfaceCapture, Entries template\s+(\d+)', 11)
test.file_grep(test.stats, r'IfaceCapture, Entries cloned\s+(\d+)', 14)
test.file_grep(test.stats, r'IfaceCapture, Ledger fixups in V3Param\s+(\d+)', 5)
test.file_grep(test.stats, r'IfaceCapture, Wrong-clone refs fixed\s+(\d+)', 10)
test.file_grep(test.stats, r'IfaceCapture, Dead refs fixed in modules\s+(\d+)', 0)

test.execute()

test.passes()
