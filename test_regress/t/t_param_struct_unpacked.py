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

test.compile(verilator_flags2=["--binary", "-fno-inline"])

# Instances given equal values share a specialization, wherever the values came from
if test.vlt_all:
    test.file_grep_count(test.obj_dir + "/" + test.vm_prefix + "__Syms.h",
                         r'#include "\w+_leaf(__\w+)?\.h"', 10)

test.execute()

test.passes()
