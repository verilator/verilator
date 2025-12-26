#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2025 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('simulator')

# TODO if make this general purpose, consider an e.g. VERILATOR_RUNTIME_FLAGS
# envvar so can set for test suites. Make sure runtime-debug prints such options.
test.compile(verilator_flags2=['--binary', '--debug-runtime-timeout 1'])

test.execute(fails=True, expect_filename=test.golden_filename)

test.passes()
