#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('simulator')

test.compile(verilator_flags2=["--binary", "-fno-slice"])

files = test.glob_some(test.obj_dir + "/" + test.vm_prefix + "___024root*.cpp")
test.file_grep_any(files, r'VL_CVT_UNPACK_TO_UNPACK<0, 1, 0, 0, 1>')

test.execute()

test.passes()
