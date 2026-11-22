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
test.top_filename = "t/t_config_work.v"

# Module m3 is in two libraries, both copies are emitted with their source name
test.lint(verilator_flags2=[
    '--work liba', 't/t_config_work__liba.v', '--work libb', 't/t_config_work__libb.v',
    '-libmap t_config_work.map', '--dumpi-tree 9 --dumpi-V3EmitV 9 --debug-emitv'
])

test.files_identical(test.glob_one(test.obj_dir + "/" + test.vm_prefix + "_*_widthcommit.tree.v"),
                     test.golden_filename)

test.passes()
