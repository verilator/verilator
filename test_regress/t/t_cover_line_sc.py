#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('simulator')
test.top_filename = "t/t_cover_line.v"

test.compile(verilator_flags2=['--sc --coverage-line +define+ATTRIBUTE'])

test.execute()

# Read the input .v file and do any CHECK_COVER requests
test.inline_checks()

test.passes()
