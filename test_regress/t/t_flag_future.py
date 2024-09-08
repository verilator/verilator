#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt')

test.lint(verilator_flags2=[
    "--lint-only --future0 thefuture --future1 thefuturei --thefuture -thefuture +thefuture --thefuturei 1 -Wfuture-FUTURE1 -Wfuture-FUTURE2"
])

test.passes()
