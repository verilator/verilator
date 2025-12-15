#!/usr/bin/env python3
# DESCRIPTION: Verilator: Test for property if/else assertions
#
# This file ONLY is placed under the Creative Commons Public Domain, for
# any use, without warranty, 2025 by Wilson Snyder.
# SPDX-License-Identifier: CC0-1.0

import vltest_bootstrap

test.scenarios('vlt')

test.compile(v_flags2=['--assert'])

test.execute()

test.passes()
