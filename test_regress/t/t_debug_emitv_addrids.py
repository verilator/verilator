#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2024 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt')
test.fourstate_capable = False
test.top_filename = "t/t_debug_emitv.v"

test.lint(
    # We also have dump-tree turned on, so hit a lot of AstNode*::dump() functions
    # Likewise XML
    # --Wno-COVERIGN: shares t_debug_emitv.v, whose cg_trans uses a goto-repetition transition
    # bin ([->N]); the count is unsupported (dropped) but the bin is still created with a
    # non-NONE VTransRepType.
    v_flags=["--lint-only --dumpi-tree 9 --dump-tree-addrids --Wno-COVERIGN"])

test.passes()
