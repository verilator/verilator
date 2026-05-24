#!/usr/bin/env python3
# DESCRIPTION: Verilator: Test pullup/pulldown bus propagation through whole-vector ports
#
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: CC0-1.0

import vltest_bootstrap

test.scenarios('simulator')

test.compile()

test.execute()

test.passes()
