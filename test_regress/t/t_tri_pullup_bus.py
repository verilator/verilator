#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: CC0-1.0

import vltest_bootstrap

test.scenarios('simulator')

# Bound regressions that expand the wide streams into individual bit drivers.
test.timeout(120)

test.compile(timing_loop=True, verilator_flags2=['--timing'])

test.execute()

test.passes()
