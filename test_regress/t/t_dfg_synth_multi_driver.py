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

test.scenarios('vlt')

SIZE_SMALL = 4000
# Linear scaling gives 4x, guard against quadratic growth
SIZE_LARGE = SIZE_SMALL * 4
MAX_RATIO = 8
MIN_SECONDS = 0.01


def compile_time(size):
    mdir = test.obj_dir + "/obj_" + str(size)
    test.lint(verilator_flags2=["--stats", "--no-debug-check", "-GN=" + str(size), "-Mdir", mdir],
              make_main=False,
              verilator_make_gmake=False)
    stats_filename = mdir + "/V" + test.name + "__stats.txt"
    stats = test.file_contents(stats_filename)
    match = re.search(r'Stage, Elapsed time \(sec\), \d+_dfg-synthesize\s+(\S+)', stats)
    if not match:
        test.error("DFG synthesis time not found in " + stats_filename)
    return float(match.group(1))


small = compile_time(SIZE_SMALL)
large = compile_time(SIZE_LARGE)
print(f"DFG synthesis: {SIZE_SMALL} drivers in {small:.3f}s, "
      f"{SIZE_LARGE} drivers in {large:.3f}s ({large / small:.1f}x)")
if large > MIN_SECONDS and large > small * MAX_RATIO:
    test.error("DFG synthesis time scaled superlinearly with driver count: " +
               f"{SIZE_SMALL} drivers took {small:.3f}s, " +
               f"{SIZE_LARGE} drivers took {large:.3f}s (over {MAX_RATIO}x)")

test.passes()
