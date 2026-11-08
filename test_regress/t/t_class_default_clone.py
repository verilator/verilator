#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('simulator')

test.compile()
test.execute()
test.passes()
