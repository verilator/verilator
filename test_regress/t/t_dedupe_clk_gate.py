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

out_filename = test.obj_dir + "/V" + test.name + ".tree.json"

test.compile(verilator_flags2=["--no-json-edit-nums", "--stats"])

if test.vlt_all:
    test.file_grep(
        out_filename,
        r'{"type":"VAR","name":"t.f0.clock_gate.clken_latched","addr":"[^"]*","loc":"\w,44:[^"]*","dtypep":"\(\w+\)",.*"origName":"clken_latched",.*"isLatched":true,.*"dtypeName":"logic"'
    )
    test.file_grep(test.stats, r'Optimizations, Gate sigs deduped\s+(\d+)', 4)

test.passes()
