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

# Ratio of the parameter widths
SIZE_RATIO = 16
# Allowance over linear scaling for timer noise
SLACK = 4
PARAM_BITS_SMALL = 512
PARAM_BITS_LARGE = PARAM_BITS_SMALL * SIZE_RATIO
MAX_RATIO = SIZE_RATIO * SLACK
# Ignore the ratio when Verilation is fast enough that timer noise dominates
MIN_SECONDS = 0.1


def verilation_seconds(param_bits):
    # In a directory of its own, as file_grep() caches the contents of each file it reads
    mdir = test.obj_dir + "/obj_" + str(param_bits)
    test.lint(verilator_flags2=["--stats", "-GW=" + str(param_bits), "-Mdir", mdir])
    stats_filename = mdir + "/V" + test.name + "__stats.txt"
    return float(test.file_grep(stats_filename, r'Stage, Elapsed time \(sec\), TOTAL\s+(\S+)')[0])


small_seconds = verilation_seconds(PARAM_BITS_SMALL)
large_seconds = verilation_seconds(PARAM_BITS_LARGE)
if large_seconds > MIN_SECONDS and large_seconds > small_seconds * MAX_RATIO:
    test.error("Verilation time scaled superlinearly with parameter width: " +
               f"{PARAM_BITS_SMALL} bits took {small_seconds:.3f}s, " +
               f"{PARAM_BITS_LARGE} bits took {large_seconds:.3f}s (over {MAX_RATIO}x)")

test.passes()
