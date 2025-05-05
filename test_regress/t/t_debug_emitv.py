#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios("vlt")

test.lint(
    # We also have dump-tree turned on, so hit a lot of AstNode*::dump() functions
    # Likewise XML
    v_flags=["--lint-only --dumpi-tree 9 --dumpi-V3EmitV 9 --debug-emitv"])

output_vs = test.glob_some(test.obj_dir + "/" + test.vm_prefix + "_*_width.tree.v")

for output_v in output_vs:
    test.files_identical(output_v, test.golden_filename)

if test.verbose:
    # Print if that the output Verilog is clean
    # TODO not yet round-trip clean
    test.run(
        cmd=[
            os.environ["VERILATOR_ROOT"] + "/bin/verilator",
            "--lint-only",
            output_vs[0],
        ],
        logfile=test.obj_dir + "/sim_roundtrip.log",
        fails=True,
        verilator_run=True,
    )

test.passes()
