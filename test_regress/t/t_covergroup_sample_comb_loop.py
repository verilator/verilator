#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap
import coverage_covergroup_common

test.scenarios('vlt_all')

# A sample() reached from combinational logic is deliberately left unordered against what it
# samples: calling sample() must not make the calling block behave as if sensitive to what the
# covergroup reads.  Unordered is not the same as unsafe -- the access is still recorded for the
# MTask data hazard fixer -- so the run must still be race free.  ThreadSanitizer is what checks
# that, and --no-threads-coarsen keeps the sample and the writer of what it samples in separate
# MTasks so there is something for it to catch.
test.enable_tsan()

# Note on the golden: because these samples are unordered, which value each one observes follows
# from how ordering resolved the loop, not from anything the LRM pins down.  The counts are
# reproducible (identical across vlt and vltmt), so they are worth locking down -- but a future
# diff here means the schedule changed, and wants understanding rather than regenerating.
coverage_covergroup_common.run(test,
                               verilator_flags2=(['--no-threads-coarsen'] if test.vltmt else []),
                               threads=(2 if test.vltmt else 1))
