#!/usr/bin/env python3
# DESCRIPTION: Verilator: reject a failed active unbounded consecutive repetition
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios("vlt")

# Side-effecting functions in assertion Boolean expressions are illegal.
test.lint(expect_filename=test.golden_filename,
          verilator_flags2=["--assert --timing +define+TEST_IMPURE_ENDPOINT"],
          fails=True)

test.compile(verilator_flags2=["--binary", "--assert", "--timing"])

test.execute()

test.passes()
