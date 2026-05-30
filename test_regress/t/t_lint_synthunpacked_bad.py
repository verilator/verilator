#!/usr/bin/env python3
# DESCRIPTION: Verilator: Lint test for SYNTHUNPACKED warning
#
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: CC0-1.0

import vltest_bootstrap

test.scenarios('linter')

test.lint(fails=True, v_flags2=['-Wwarn-SYNTHUNPACKED'], expect_filename=test.golden_filename)

test.passes()
