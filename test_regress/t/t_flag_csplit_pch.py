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

# --output-split triggers PCH generation (.gch files) for parallel builds
test.compile(verilator_flags2=["--output-split 1", "--output-split-cfuncs 1"])

# Verify PCH header was generated
test.glob_some(test.obj_dir + "/*__pch.h")

# Verify split files were produced
test.glob_some(test.obj_dir + "/*__1.cpp")

# Verify parallel builds enabled
test.file_grep(test.obj_dir + "/" + test.vm_prefix + "_classes.mk", r'VM_PARALLEL_BUILDS\s*=\s*1')

test.execute()

test.passes()
