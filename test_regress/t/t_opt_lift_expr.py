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

# -fno-const-before-dfg keeps V3Const from folding AstLogIf into AstLogOr,
# which is the only way V3LiftExpr ever encounters an AstLogIf. Option
# -fno-const-before-dfg itself is needed for testing Dfg, so needs to work.
test.compile(verilator_flags2=['--binary', '--stats', '-fno-const-before-dfg', test.pli_filename])

test.execute()

test.file_grep(test.stats, r'LiftExpr, lifted LogAnd\s+(\d+)', 16)
test.file_grep(test.stats, r'LiftExpr, lifted LogOr\s+(\d+)', 16)
test.file_grep(test.stats, r'LiftExpr, lifted LogIf\s+(\d+)', 16)
test.file_grep(test.stats, r'LiftExpr, lifted Cond\s+(\d+)', 32)
test.file_grep(test.stats, r'LiftExpr, lifted calls\s+(\d+)', 178)
test.file_grep(test.stats, r'LiftExpr, lifted impure expressions\s+(\d+)', 2)
test.file_grep(test.stats, r'LiftExpr, temporaries created\s+(\d+)', 196)
test.file_grep(test.stats, r'LiftExpr, temporaries reused\s+(\d+)', 16)

test.passes()
