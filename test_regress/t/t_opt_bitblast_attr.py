#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import re

import vltest_bootstrap

test.scenarios('vlt_all')

test.compile(verilator_flags2=['--stats', '--trace-vcd'])

test.execute()

# Each variable expected to be split is marked in the source, see the header comment there
contents = test.file_contents(test.top_filename)
nSplits = [int(n) for n in re.findall(r'// Split (\d+)', contents)]
if len(nSplits) != contents.count('// Split'):
    test.error("All '// Split' markers must give the number of fragments")
test.file_grep(test.stats, r'Optimizations, Bitblast, variables split due to attribute\s+(\d+)',
               len(nSplits))
test.file_grep(test.stats, r'Optimizations, Bitblast, variables split automatically\s+(\d+)', 0)
test.file_grep(test.stats, r'Optimizations, Bitblast, fragments created\s+(\d+)', sum(nSplits))
test.file_grep(test.stats, r'Optimizations, Bitblast, assignments through temporary\s+(\d+)', 1)

test.passes()
