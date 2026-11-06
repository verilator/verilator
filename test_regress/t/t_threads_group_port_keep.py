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

prefix = test.vm_prefix
for threads in (1, 2):
    test.clean_objs()
    test.vm_prefix = prefix + f"_{threads}"
    test.stats = f"{test.obj_dir}/{test.vm_prefix}__stats.txt"
    test.compile(verilator_flags2=["--binary", "--stats"], threads=threads)
    test.execute()
    if threads == 1:
        # A group inlined with one thread no longer keeps its ports
        test.file_grep(test.stats, r'Optimizations, DFG, DfgToAst, output variables\s+(\d+)', 5)
    else:
        # The sub input connected to a kept port is kept too
        test.file_grep(test.stats, r'Optimizations, DFG, DfgToAst, var refs substituted\s+(\d+)',
                       16)
        # The split elements of a kept array port are kept, so the instances share code
        test.file_grep(test.stats, r'Optimizations, Combined CFuncs\s+(\d+)', 9)

test.passes()
