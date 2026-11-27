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

test.compile(verilator_flags2=["--binary"])

test.execute()

if test.vlt_all:
    # Base methods must stay plain functions, only their killing overrides are coroutines
    prefix = test.obj_dir + "/" + test.vm_prefix + "_t__03A__03A"
    test.file_grep(prefix + "base_killer.h", r'void init\(')
    test.file_grep(prefix + "base_plain.h", r'void __VnoInFunc_hidden\(')
    test.file_grep(prefix + "base_plain.h", r'void __VnoInFunc_rechained\(')

test.passes()
