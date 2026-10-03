#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# Copyright 2026 Yutetsu TAKATSUKASA
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap
from subgraph_test_common import check_subgraph_specializations

test.scenarios("vlt")
test.top_filename = "t/t_subgraph_schedule_dual.sv"
test.sim_time = 7000

tree_filename = test.obj_dir + "/V" + test.name + "_010_linkdotparam.tree.json"

test.compile(
    verilator_flags2=["--subgraph-schedule -Wno-fatal --dump-tree-json --no-json-edit-nums"])
test.execute(expect_filename="t/t_subgraph_schedule_dual.out")

check_subgraph_specializations(test, tree_filename, "sg_dual_node")

test.passes()
