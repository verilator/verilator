#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

noinline = "noinl" in test.name
if not noinline:
    test.priority(30)
test.scenarios('vlt_all')
test.top_filename = "t/t_hier_block.v"
test.golden_filename = "t/t_hier_block_trace_saif.out"

verilator_common_flags = [
    't/t_hier_block.cpp',
    '--Wno-TIMESCALEMOD',
    '--trace-saif',
    '--trace-underscore',  # Should not trace handle
    "--trace-max-width",
    "0",
    "--trace-max-array",
    "0",
    "--trace-structs",
]

verilator_hier_flags = verilator_common_flags + ['--hierarchical']
if noinline:
    verilator_hier_flags.extend(["+define+NO_INLINE"])

# Compile hierarchically
test.vm_prefix = "Vhier"
test.main_filename = test.obj_dir + "/Vhier__main.cpp"
test.compile(verilator_flags2=verilator_hier_flags)

# Compile non hierarchically
test.vm_prefix = "Vnonh"
test.main_filename = test.obj_dir + "/Vnonh__main.cpp"
test.compile(verilator_flags2=verilator_common_flags)

trace_hier = test.trace_filename.replace("simx", "hier")
trace_nonh = test.trace_filename.replace("simx", "nonh")

# Run the hierarchical model
test.execute(executable=test.obj_dir + "/Vhier")
test.run(cmd=["mv", test.trace_filename, trace_hier])
# Run the non hierarchical model
test.execute(executable=test.obj_dir + "/Vnonh")
test.run(cmd=["mv", test.trace_filename, trace_nonh])

# The two models must match
test.saif_identical(trace_hier, trace_nonh)
# The hierarchical must match the reference
test.saif_identical(trace_hier, test.golden_filename.replace("_noinl", ""))

test.passes()
