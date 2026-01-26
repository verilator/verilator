#!/usr/bin/env python3
# DESCRIPTION: Verilator: Test for false positive UNUSEDSIGNAL in unused functions
#
# Copyright 2026 by Wilson Snyder.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('linter')

# This test should NOT produce a UNUSEDSIGNAL warning for parameter 'n' in unused function
test.lint()

test.passes()
