#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt')
test.top_filename = "t/t_gen_alw.v"  # Use any top file

test.init_benchmarksim()

# As an example, compile and simulate the top file with varying optimization level
l_opts = [1, 2, 3]

for l_opt in l_opts:
    test.compile(benchmarksim=1, v_flags2=["-O" + str(l_opt)])

    test.execute()

filename = test.benchmarksim_filename
gotn = 0
with open(filename, 'r', encoding="utf8") as fh:
    lineno = 0
    headered = False
    for line in fh:
        lineno += 1
        if re.match(r'^#', line):
            continue
        if not headered:
            headered = True
            if not re.search(r'evals, ', line):
                test.error(filename + ":" + str(lineno) + ": Expected header but found: " + line)
        else:
            m = re.search(r'(\d+\.?\d*),(\d+\.?\d*)', line)
            if not m:
                test.error(filename + ":" + str(lineno) + ": Expected 2 tokens on line: " + line)
                continue
            cycles = float(m.group(1))
            time = float(m.group(2))
            if cycles <= 0.0 or time <= 0.0:
                test.error(filename + ":" + str(lineno) + ": Invalid data on line: " + line)
                continue
            gotn += 1

n_lines_expected = len(l_opts)
if gotn != int(n_lines_expected):
    test.error("Expected " + str(n_lines_expected) + " lines but found " + str(gotn))

test.passes()
