#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This file ONLY is placed under the Creative Commons Public Domain.
# SPDX-FileCopyrightText: Copyright 2026 Google LLC
# SPDX-License-Identifier: CC0-1.0

import vltest_bootstrap

test.scenarios('simulator')

if not test.have_solver:
    test.skip("No constraint solver installed")

# Allow the UNSIGNED warning which is expected for 'byte >= 0'
test.compile(verilator_flags2=['-Wno-UNSIGNED', '-LDFLAGS', '-lpthread'])

test.execute()

test.passes()
