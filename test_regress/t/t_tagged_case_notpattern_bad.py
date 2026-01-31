#!/usr/bin/env python3
# DESCRIPTION: Verilator: Test for case-matches with non-pattern condition
#
# This file ONLY is placed under the Creative Commons Public Domain, for
# any use, without warranty, 2026 by Wilson Snyder.
# SPDX-License-Identifier: CC0-1.0

import vltest_bootstrap

test.scenarios('vlt')
test.top_filename = "t/t_tagged_case_notpattern_bad.v"

test.lint(
    fails=True,
    expect_filename=test.golden_filename,
)

test.passes()
