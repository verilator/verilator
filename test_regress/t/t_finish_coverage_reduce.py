#!/usr/bin/env python3
# DESCRIPTION: Verilator: Finish-capable calls are not cloned by expression coverage
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import re

import vltest_bootstrap

test.scenarios('vlt')

test.compile(verilator_flags2=['--cc', '--coverage-expr'])

hot_filename = test.obj_dir + '/V' + test.name + '___024root__0.cpp'
generated = test.file_contents(hot_filename)
finish_calls = len(re.findall(r'VL_FINISH_MT\(', generated))
if finish_calls != 1:
    test.error(f'Expected one generated finish call, got {finish_calls}')

test.passes()
