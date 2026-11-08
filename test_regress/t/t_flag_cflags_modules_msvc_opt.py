#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
import vltest_bootstrap

test.scenarios('vlt')
test.top_filename = test.t_dir + '/t_flag_cflags_modules_msvc.v'
test.clean_objs()

test.lint(verilator_flags2=[
    '--compiler msvc',
    '--exe',
    test.t_dir + '/t_flag_cflags_modules_msvc.ixx',
])
test.file_grep_not(test.obj_dir + '/vlt_compile.log',
                   r'Unsupported: C\+\+ module interface files')
test.passes()
