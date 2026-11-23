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

test.compile(verilator_flags2=["--stats"])

removed = ("EmptyBase", "EmptyDerived", "Outer", "InnerEmpty", "PlainDerived", "ParamClass",
           "LocalParam")

# A class without a class package is declared in its own header
for name in removed:
    test.glob_one(test.obj_dir + "/*" + name + ".h")

# A class with a class package is declared in the class package header
for name in ("StaticVar", "StaticFunc", "StaticVoid", "StaticBase", "Inner", "OuterStatic",
             "UnpackedStruct"):
    test.glob_one(test.obj_dir + "/*" + name + "__Vclpkg.h")

test.file_grep(test.stats, r'Optimizations, Empty class packages deleted\s+(\d+)', len(removed))

test.execute()

test.passes()
