#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt')

test.compile(verilator_flags2=['--assert'])

# a is always 1 so there is no per-cycle safety failure: the ONLY failure source
# is the strong end-of-simulation liveness obligation of s_always[1:1] (its window
# is cut off by $finish), so the simulation must exit non-zero. If the in-window
# marking regresses (e.g. the offset-hi vertex stops being flagged), s_always[1:1]
# goes silent, the run succeeds, and this test fails -- catching the regression.
test.execute(fails=True)

test.passes()
