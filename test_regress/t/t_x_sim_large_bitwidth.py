#!/usr/bin/env python3
# DESCRIPTION: Verilator: Test X/Z four-state simulation with larger bit widths
#
# This test verifies X and Z value propagation in 64/128/256-bit operations.
#
# SPDX-FileCopyrightText: 2026
# SPDX-License-Identifier: LGPL-3.0-only

import vltest_bootstrap

test.scenarios('simulator')

test.compile(verilator_flags2=['--binary', '--fourstate'])

test.execute()

test.passes()
