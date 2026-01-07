#!/usr/bin/env python3
# DESCRIPTION: Verilator: Test for false positive UNUSEDSIGNAL in unused functions
#
# Copyright 2026.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('linter')

# This test should NOT produce a UNUSEDSIGNAL warning for parameter 'n' in unused function
test.lint(verilator_flags2=[
    "--lint-only --assert --quiet-stats --top-module foo --default-language 1364-1995 -Wall -Wno-fatal"
],
          fails=False)

test.passes()
