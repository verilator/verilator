#!/usr/bin/env python3
# DESCRIPTION: Verilator: Converge dependent localparams after parameterized class linking
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Petr Nohavica
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt')

test.compile(verilator_flags2=["--binary", "--stats"])

test.file_grep(test.stats, r'Elab, projection facts\s+(\d+)', 2)
test.file_grep(test.stats, r'Elab, projections published\s+(\d+)', 1)
test.file_grep(test.stats, r'Elab, retired projections\s+(\d+)', 1)
test.file_grep(test.stats, r'Elab, deferred parameter facts\s+(\d+)', 2)
test.file_grep(test.stats, r'Elab, deferred parameters published\s+(\d+)', 2)

test.execute()

test.passes()
