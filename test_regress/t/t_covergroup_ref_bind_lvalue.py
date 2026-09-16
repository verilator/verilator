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
test.fourstate_capable = False

# Sampling what a non-blocking assignment writes is a data race if left unordered, but whether
# it changes the histogram in any one run is timing dependent, so use ThreadSanitizer to detect
# it reliably. --no-threads-coarsen keeps the sample and the writer in separate MTasks.
test.enable_tsan()

coverage_covergroup_common.run(test,
                               verilator_flags2=(['--stats'] +
                                                 (['--no-threads-coarsen'] if test.vltmt else [])),
                               threads=(2 if test.vltmt else 1))

# No sample names a covergroup object, so each resolves to the union over its type's two
# constructions rather than to one instance
test.file_grep(test.stats, r'Scheduling, covergroup ref sample calls, per instance\s+(\d+)', 0)
test.file_grep(test.stats, r'Scheduling, covergroup ref sample calls, per type\s+(\d+)', 4)
