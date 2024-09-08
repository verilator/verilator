#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap
import time

test.scenarios('dist')

if 'VERILATOR_TEST_RANDOM_FAILURE' not in os.environ:
    print("Test is for harness checking only, setenv VERILATOR_TEST_RANDOM_FAILURE=1")
    test.passes()
else:
    # Randomly fail to test driver.py
    t = time.time()
    if t % 2:
        test.error("random failure " + str(t))

    test.passes()
