#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt')

if 'VERILATOR_TEST_NO_GDB' in os.environ:
    test.skip("Skipping due to VERILATOR_TEST_NO_GDB")

test.lint(
    # Check we can call dump() on graph, and other things
    v_flags=["--lint-only --debug --debugi-V3GraphTest 9 --debug-self-test"])

test.passes()
