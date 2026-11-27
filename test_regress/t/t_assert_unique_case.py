#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2024 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

from pathlib import Path

import vltest_bootstrap

test.scenarios('simulator')
test.top_filename = "t/t_assert_unique_case_bad.v"

test.compile(verilator_flags2=["-x-assign 0 --assert-case --no-stop-fail +define+NO_STOP_FAIL"])

test.execute()

# The driver process can finish before or after the independent case checks in
# the same time step. Check the marker exactly once and retain all diagnostics
# and branch reports in their original order.
for source, target in ((test.run_log_filename, 'actual'), (test.golden_filename, 'expected')):
    lines = Path(source).read_text(encoding="utf8").splitlines(keepends=True)
    marker = '*-* All Finished *-*'
    assert sum(line.strip() == marker for line in lines) == 1
    (Path(test.obj_dir) / (target + '.log')).write_text(''.join(line for line in lines
                                                                if line.strip() != marker),
                                                        encoding="utf8")
test.files_identical(test.obj_dir + '/actual.log', test.obj_dir + '/expected.log', is_logfile=True)

test.passes()
