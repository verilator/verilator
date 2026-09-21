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

SIZE_SMALL = 512
SIZE_LARGE = SIZE_SMALL * 4
# Linear scaling gives 4x, quadratic gives 16x
MAX_RATIO = 8
# Ignore the ratio when scheduling is fast enough that timer noise dominates
MIN_SECONDS = 0.1
# Peak memory limit at the small size (about 50 MB when fine, over 2000 MB when quadratic)
MAX_MB = 500


def compile_stats(size):
    test.compile(verilator_flags2=["--stats", "--no-debug-check", "-GArraySize=" + str(size)],
                 make_main=False,
                 verilator_make_gmake=False)
    with open(test.stats, "r", encoding="utf-8") as fh:
        stats = fh.read()
    times = re.findall(r'Stage, Elapsed time \(sec\), \d+_sched\S*\s+(\S+)', stats)
    peak = re.search(r'Peak Memory Usage \(MB\)\s+(\S+)', stats)
    if not times or not peak:
        test.error("Scheduling time or peak memory not found in " + test.stats)
    return sum(float(t) for t in times), float(peak.group(1))


small, small_mb = compile_stats(SIZE_SMALL)
# Do not build the large size if memory already blew up
if small_mb > MAX_MB:
    test.error(f"Peak memory with {SIZE_SMALL} forced array elements was {small_mb:.0f} MB " +
               f"(over {MAX_MB} MB)")
large, _ = compile_stats(SIZE_LARGE)
if large > MIN_SECONDS and large > small * MAX_RATIO:
    test.error("Scheduling time scaled superlinearly with forced array size: " +
               f"{SIZE_SMALL} elements took {small:.3f}s, " +
               f"{SIZE_LARGE} elements took {large:.3f}s (over {MAX_RATIO}x)")

test.passes()
