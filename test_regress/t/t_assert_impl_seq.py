#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test module - implication with sequence expressions
#
# Tests SVA implication (|->) with sequence expressions on the RHS
# This is the pattern used in mbits UART VIP assertions.
#
# This file ONLY is placed under the Creative Commons Public Domain, for
# any use, without warranty, 2025 by Wilson Snyder.
# SPDX-License-Identifier: CC0-1.0

import vltest_bootstrap

test.scenarios('vlt')
test.top_filename = "t/t_assert_impl_seq.v"

test.compile(verilator_flags2=['--timing', '--assert'])

test.execute()

test.passes()
