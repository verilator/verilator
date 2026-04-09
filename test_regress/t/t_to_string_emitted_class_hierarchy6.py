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
test.top_filename = "t/t_to_string_emitted_class_hierarchy.v"

obj_type = "Derived4"
printed_from_type = "Derived4"
obj_type2 = "Derived9"
printed_from_type2 = "Derived9"
expected_to_string_classes = [
    "Base", "Derived1", "Derived2", "Derived3", "Derived4", "IClass1", "Derived7", "Derived8",
    "Derived9"
]

test.compile(verilator_flags2=[
    "--stats", f"-DOBJ_TYPE={obj_type}", f"-DPRINTED_FROM_TYPE={printed_from_type}",
    f"-DOBJ_TYPE2={obj_type2}", f"-DPRINTED_FROM_TYPE2={printed_from_type2}"
])
for class_name in expected_to_string_classes:
    test.file_grep(
        f"{test.obj_dir}/{test.vm_prefix}___024unit__03a__03a{class_name}__Vclpkg__0.cpp",
        f"std::string {test.vm_prefix}___024unit__03a__03a{class_name}::to_string()")
test.file_grep(test.stats, r"Optimizations, Class ToString emitted\s+(\d+)",
               len(expected_to_string_classes))
test.execute()
test.files_identical(test.obj_dir + "/vlt_sim.log", test.golden_filename, "logfile")

test.passes()
