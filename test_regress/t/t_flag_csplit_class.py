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

test.compile(verilator_flags2=["--binary", "--output-split 32"])

EXPECTED_FILES = 3
files = test.glob_some(test.obj_dir + "/" + test.vm_prefix + "__Classes_*.cpp")
if len(files) != EXPECTED_FILES:
    test.error("Expecting " + str(EXPECTED_FILES) + " class files, got " + str(len(files)))

test.execute()

test.passes()
