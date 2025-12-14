#!/usr/bin/env python3
# DESCRIPTION: Verilator: Issue #6814 - Inherited type parameters
#
# This file ONLY is placed under the Creative Commons Public Domain, for
# any use, without warranty, 2025 by Verilator Authors.
# SPDX-License-Identifier: CC0-1.0

import vltest_bootstrap

test.scenarios('vlt')
test.compile()
test.execute()

test.passes()
