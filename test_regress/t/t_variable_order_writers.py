#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vltmt')

test.compile(verilator_flags2=['--stats', '--threads-max-mtasks 8', '-Wno-UNOPTTHREADS'],
             threads=2)

# State written by different workers starts in separate storage groups.
if test.repcut:
    test.file_grep(test.stats, r'VariableOrder, RepCut storage groups\s+(\d+)', 2)
    test.file_grep(test.stats, r'VariableOrder, RepCut reader groups\s+(\d+)', 2)
else:
    test.file_grep(test.stats, r'VariableOrder, MTask aligned group starts\s+([2-9]|\d\d+)')

test.execute()

test.passes()
