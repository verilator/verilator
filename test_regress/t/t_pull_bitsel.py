#!/usr/bin/env python3
# DESCRIPTION: Verilator: Test pullup/pulldown on bus bit-selects via wrapper
#
# This file ONLY is placed under the Creative Commons Public Domain, for
# any use, without warranty, 2026 by Lucas Amaral.
# SPDX-License-Identifier: CC0-1.0

import vltest_bootstrap

test.scenarios('simulator')

test.compile()

test.execute()

test.passes()