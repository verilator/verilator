#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('linter')

# MULTIDRIVENPROC is off by default; enable it explicitly. Module 't' (same
# clock) triggers it; module 't2' (different clocks) is reported by MULTIDRIVEN
# instead, confirming MULTIDRIVENPROC is suppressed there.
# -Wno-MULTITOP: both modules are top-level here on purpose (two independent
# demonstrations), so silence the unrelated multiple-top-module warning.
test.lint(fails=True,
          verilator_flags2=['-Wwarn-MULTIDRIVENPROC', '-Wno-MULTITOP'],
          expect_filename=test.golden_filename)

test.extract(in_filename=test.top_filename,
             out_filename=test.root + "/docs/gen/ex_MULTIDRIVENPROC_faulty.rst",
             lines="15-16")

test.extract(in_filename=test.golden_filename,
             out_filename=test.root + "/docs/gen/ex_MULTIDRIVENPROC_msg.rst",
             lines="1-5")

test.passes()
