#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2024 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt')

# Some cases specifically exercise the no-timing fallback: simple per-instance events use
# best-effort in-class assignment instrumentation, and unsupported cases warn.
test.lint(verilator_flags2=['--no-timing'], expect_filename=test.golden_filename, fails=True)

test.compile(verilator_flags2=['--Wno-COVERIGN', '--no-skip-identical', '--no-timing'])

test.execute()

test.passes()
