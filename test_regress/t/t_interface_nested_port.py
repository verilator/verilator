#!/usr/bin/env python3
# DESCRIPTION: Verilator: Test nested interface as port connection
# Issue #5066
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2024 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('simulator')

test.compile(verilator_flags2=['--no-timing', '-Wno-STMTDLY'])

test.execute()

test.passes()
