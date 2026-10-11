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

test.scenarios('vlt_all')
test.top_filename = 't/t_covergroup_cross_with.v'
test.v_flags2 += ['t/t_covergroup_cross_with.cpp']

test.compile(verilator_flags2=[
    '--coverage-user', '--protect-ids', '--protect-key CROSS_WITH_KEY', '-Wno-INSECURE'
],
             threads=(2 if test.vltmt else 1))
test.execute()

names = r'cg_select|cg_runtime|t_covergroup_cross_with\.v|sv_function|neg_lo_one|high_even'
test.file_grep_not(test.coverage_filename, names)
# A filter passes its bin's name and file to the runtime, for a warning
filters = 0
for filename in test.glob_some(test.obj_dir + "/*.cpp"):
    for line in test.file_contents(filename).splitlines():
        if 'withBegin(' in line:
            filters += 1
            if re.search(names, line):
                test.error("Unprotected identifier: " + line)
if not filters:
    test.error("No 'with' filter found")

test.passes()
