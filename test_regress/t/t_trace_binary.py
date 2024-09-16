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

test.compile(
    verilator_flags=[  # Custom as don't want -cc
        "-Mdir " + test.obj_dir, "--debug-check"
    ],
    verilator_flags2=['--binary --trace'])

test.execute()

test.vcd_identical(test.trace_filename, test.golden_filename)

test.passes()
