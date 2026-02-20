#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2024 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt')

if test.have_dev_gcov:
    test.skip("Too slow with code coverage")

test.top_filename = f"{test.obj_dir}/in.v"

with open(test.top_filename, "w", encoding="utf8") as f:
    f.write("module top;\n")
    for i in range(50000):
        f.write(f"  int x{i} = 'd{i};\n")
    f.write("endmodule\n")

test.timeout(30 if not test.have_dev_asan else 60)

test.lint(verilator_flags2=[f"--max-num-width {2**29}"])

test.passes()
