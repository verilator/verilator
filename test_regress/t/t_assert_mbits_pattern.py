#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test module - mbits assertion pattern test
#
# Tests SVA patterns used in mbits:
# - first_match()
# - ##[min:max] range delays
# - property if/else
#
# This file ONLY is placed under the Creative Commons Public Domain, for
# any use, without warranty, 2025 by Wilson Snyder.
# SPDX-License-Identifier: CC0-1.0

import vltest_bootstrap

test.scenarios('vlt')
test.top_filename = "t/t_assert_mbits_pattern.v"

test.compile(verilator_flags2=['--timing', '--assert'])

test.execute()

test.passes()
