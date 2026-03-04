#!/usr/bin/env python3
# DESCRIPTION: Verilator: Test X/Z four-state simulation with time functions
#
# This test verifies X and Z value propagation with $time, $stime, $realtime.
#
# SPDX-FileCopyrightText: 2026
# SPDX-License-Identifier: LGPL-3.0-only

import vltest_bootstrap

test.scenarios('simulator')

test.compile(verilator_flags2=['--binary', '--fourstate', '-Wno-WIDTHTRUNC', '-Wno-WIDTHEXPAND'])

test.execute()

test.passes()
