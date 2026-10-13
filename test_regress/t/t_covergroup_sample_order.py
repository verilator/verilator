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

# An unordered sample() is a genuine data race, but whether it changes the
# histogram in any one run is timing dependent, so use ThreadSanitizer to detect
# it reliably. --no-threads-coarsen keeps the sample and the writer of what it
# samples in separate MTasks.
test.enable_tsan()

coverage_covergroup_common.run(test,
                               verilator_flags2=(['--no-threads-coarsen'] if test.vltmt else []),
                               threads=(2 if test.vltmt else 1))
