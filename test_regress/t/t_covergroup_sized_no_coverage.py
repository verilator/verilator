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
test.top_filename = 't/t_covergroup_sized_bins.v'

# Without --coverage, and with names protected in the generated code
test.compile(verilator_flags2=['--protect-ids', '--protect-key SIZED_KEY', '-Wno-INSECURE'])

test.execute()

for filename in test.glob_some(test.obj_dir + '/*.cpp'):
    test.file_grep_not(filename, r'cg_values|cg_ieee|fixed4|dflt')

test.passes()
