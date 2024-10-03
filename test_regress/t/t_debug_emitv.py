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

test.lint(
    # We also have dump-tree turned on, so hit a lot of AstNode*::dump() functions
    # Likewise XML
    v_flags=["--lint-only --dumpi-tree 9 --dumpi-V3EmitV 9 --debug-emitv"])

test.files_identical(test.glob_one(test.obj_dir + "/" + test.vm_prefix + "_*_width.tree.v"),
                     test.golden_filename)

test.passes()
