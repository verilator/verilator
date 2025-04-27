#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('simulator')

test.compile(verilator_flags2=["--trace-vcd", "--trace-structs", "--output-split-ctrace", "32"])

if test.vlt_all:
    test.file_grep_count(test.obj_dir + "/V" + test.name + "__Trace__0.cpp",
                         r'void Vt.*trace_chg_.*sub.*{', 3)

test.execute()

test.passes()
