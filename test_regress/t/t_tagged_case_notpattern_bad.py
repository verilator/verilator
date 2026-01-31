#!/usr/bin/env python3
# DESCRIPTION: Verilator: Test for case-matches with non-pattern condition
#
# Copyright 2026 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt')
test.top_filename = "t/t_tagged_case_notpattern_bad.v"

test.lint(
    fails=True,
    expect_filename=test.golden_filename,
)

test.passes()
