#!/usr/bin/env python3
# DESCRIPTION: Verilator: Lint test for UNSYNTHESIZABLE warning
#
# SPDX-FileCopyrightText: 2026 Lucas Amaral
# SPDX-License-Identifier: CC0-1.0

import vltest_bootstrap

test.scenarios('linter')

test.lint(fails=True,
          v_flags2=['-Wwarn-UNSYNTHESIZABLE'],
          expect_filename=test.golden_filename)

test.passes()
