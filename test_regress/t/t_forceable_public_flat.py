#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2025 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt')

test.compile()

files = test.glob_some(test.obj_dir + "/" + test.vm_prefix + "*.h")
test.file_grep_any(files, r' u_sub__DOT__a__VforceRd')
test.file_grep_any(files, r' u_sub__DOT__a__VforceEn')
test.file_grep_any(files, r' u_sub__DOT__a__VforceVal')

test.passes()
