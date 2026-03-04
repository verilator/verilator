#!/usr/bin/env python3
# DESCRIPTION: Verilator: Test X initialization with --x-sim
#
# This test verifies X initialization of four-state signals when --x-sim is enabled.
#
# SPDX-FileCopyrightText: 2026
# SPDX-License-Identifier: LGPL-3.0-only

import vltest_bootstrap

test.scenarios('simulator')

test.compile(verilator_flags2=['--binary', '--four-state'])

test.execute()

test.passes()
