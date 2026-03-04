#!/usr/bin/env python3
# DESCRIPTION: Verilator: Test X/Z four-state simulation with --x-sim
#
# This test verifies X and Z value propagation when --x-sim is enabled.
#
# SPDX-FileCopyrightText: 2026
# SPDX-License-Identifier: LGPL-3.0-only

import vltest_bootstrap

test.scenarios('simulator')

test.compile(verilator_flags2=['--binary', '--fourstate'])

test.execute()

test.passes()
