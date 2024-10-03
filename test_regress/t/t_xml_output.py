#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt')

out_filename = test.obj_dir + "/renamed-" + test.name + ".xml"

test.compile(verilator_flags2=["--no-std", "--xml-only --xml-output", out_filename],
             verilator_make_gmake=False,
             make_top_shell=False,
             make_main=False)

test.files_identical(out_filename, test.golden_filename)

for filename in test.glob_some(test.obj_dir + "/*"):
    if (re.search(r'\.log', filename)  # Made by driver.py, not Verilator sources
            or re.search(r'\.status', filename)  # Made by driver.py, not Verilator sources
            or re.search(r'renamed-', filename)):  # Requested output
        continue
    test.error("%Error: Created '" + filename + "', but --xml-only shouldn't create files")

test.passes()
