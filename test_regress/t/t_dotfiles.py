#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vltmt')

# Use a top file which we are sure to be parallelizable
test.top_filename = "t/t_gen_alw.v"

test.compile(v_flags2=["--dumpi-graph 6"], threads=2)

for dotname in [
        "linkcells", "task_call", "gate_graph", "gate_final", "acyc_simp", "orderg_pre",
        "orderg_acyc", "orderg_order", "orderg_domain", "ordermv_initial", "ordermv_hazards",
        "ordermv_contraction", "ordermv_transitive1", "orderg_done", "schedule"
]:
    # Some files with identical prefix are generated multiple times during
    # Verilation. Ensure that at least one of each dotname-prefixed file is generated.
    dotFiles = test.glob_some(test.obj_dir + "/*" + dotname + ".dot")
    for dotFilename in dotFiles:
        test.file_grep(dotFilename, r'digraph v3graph')

test.passes()
