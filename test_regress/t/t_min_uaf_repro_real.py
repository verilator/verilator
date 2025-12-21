#!/usr/bin/env python3
# DESCRIPTION: Verilator: Regression test for scope/var lifetime issue
#
# This file ONLY is placed under the Creative Commons Public Domain, for
# any use, without warranty, 2025 by Wilson Snyder.
# SPDX-License-Identifier: CC0-1.0

import vltest_bootstrap

test.scenarios('simulator')
test.top_filename = "t/t_min_uaf_repro_real.sv"

test.compile(verilator_flags2=['--binary', '--timing', '--debug'])

test.execute()

test.passes()
