#!/usr/bin/env python3
# DESCRIPTION: Verilator: same-FSM combo multi-case warning test
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt')

# Two supported case statements in the same combinational always block for the
# same FSM are legal RTL, but Phase 1 only instruments the first and warns on
# the later duplicate.
test.compile(verilator_flags2=["--cc --coverage"], fails=True, expect_filename=test.golden_filename)

test.passes()
