#!/usr/bin/env python3
# DESCRIPTION: Verilator: Test X/Z four-state simulation with comparisons
#
# This test verifies X and Z value propagation with comparison operators.
#
# SPDX-FileCopyrightText: 2026
# SPDX-License-Identifier: LGPL-3.0-only

import vltest_bootstrap

test.scenarios('simulator')

test.compile(verilator_flags2=['--binary', '--four-state'])

test.execute()

test.passes()
