#!/usr/bin/env python3
# DESCRIPTION: Verilator: Test that unused function parameters still warn in used functions
#
# Copyright 2026 by Wilson Snyder.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('linter')

# This test SHOULD produce a UNUSEDSIGNAL warning for unused local variable in used function
# This is a regression test to ensure we don't suppress warnings for unused variables in used functions
# (The fix only suppresses warnings when the function itself is unused)
test.lint(fails=True, expect_filename=test.golden_filename)

test.passes()
