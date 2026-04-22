#!/usr/bin/env python3
# DESCRIPTION: Verilator: Test pullup/pulldown on bus bit-selects via wrapper
#
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: CC0-1.0

import vltest_bootstrap

test.scenarios('simulator')
test.fourstate_capable = False

test.compile()

test.execute()

test.passes()
