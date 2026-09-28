#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt_all')

test.compile()

test.execute()

files = test.glob_some(f"{test.obj_dir}/{test.vm_prefix}__Classes_*.cpp")
for cls in ('Created', 'Base'):
    for method in ('~', 'clone', 'init', '_ctor_var_reset'):
        test.file_grep_any(files, cls + '::' + method)

for filename in files:
    test.file_grep_not(filename, r'NeverVirt::(~|clone|init|_ctor_var_reset)')
    test.file_grep_not(filename, r'NeverPlain::(~|clone|init|_ctor_var_reset)')

test.passes()
