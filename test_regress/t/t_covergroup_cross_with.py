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

if test.tsan:
    test.skip("ThreadSanitizer not compatible with AddressSanitizer\n")

# A filter's cross items, which the standard names, hide others without a warning, and a filter
# may read all, some, or none of them
test.lint(verilator_flags2=['-Wwarn-UNUSEDSIGNAL', '-Wwarn-VARHIDDEN', '-Wno-fatal'])
test.file_grep_not(test.compile_log_filename, r"hides declaration in upper scope: '[ab]'")
test.file_grep_not(test.compile_log_filename, r"not used: '(a|b|aa|bb|ee|nn|pp|ss|ww|xp|yp)'")

# Also AddressSanitizer, rather than a separate _asan variant: the runtime enumerates the value
# tuples a filter reads, of wide values and excluded intervals too
coverage_covergroup_common.run(
    test,
    verilator_flags2=['-CFLAGS -fsanitize=address -LDFLAGS -fsanitize=address', test.pli_filename],
    threads=(2 if test.vltmt else 1))
