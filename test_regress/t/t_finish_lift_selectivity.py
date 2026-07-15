#!/usr/bin/env python3
# DESCRIPTION: Verilator: Finish-sensitive lifting ignores unrelated sibling statements
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt')

test.compile(verilator_flags2=['--binary', '--no-timing', '-fno-lift-expr', '--stats'])

test.file_grep(test.stats, r'LiftExpr, lifted calls\s+(\d+)', 2)
test.file_grep(test.stats, r'Finish, Finish-capable callbacks\s+(\d+)', 16)
test.file_grep(test.stats, r'Finish, Containment analysis visits\s+(\d+)', 902)
test.file_grep(test.stats, r'LiftExpr, finish analysis visits\s+(\d+)', 812)
test.file_grep(test.stats, r'Task, finish guard classifications\s+(\d+)', 8)

test.execute()

test.passes()
