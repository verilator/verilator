#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Petr Nohavica
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('simulator')

test.compile(verilator_flags2=["--stats"])

if test.vlt_all:
    test.file_grep(test.stats, r'Elab, projection facts\s+(\d+)', 3)
    test.file_grep(test.stats, r'Elab, projections published\s+(\d+)', 3)

test.execute()

test.passes()
