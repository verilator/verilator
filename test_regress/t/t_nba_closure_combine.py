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

test.compile()

# A combined closure function is deleted, so its name is gone from the generated code
funcs = set()
for filename in test.glob_some(test.obj_dir + "/" + test.vm_prefix + "*.cpp"):
    funcs.update(re.findall(r'__VnbaClosureFunc_\d+', test.file_contents(filename)))
if len(funcs) != 2:
    test.error("Expected 2 closure functions, got: " + " ".join(sorted(funcs)))

test.passes()
