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
test.top_filename = "t/t_hier_block.v"

# Both options are generated internally, never written by a user, so their
# malformed forms only need to fail cleanly rather than be diagnosed nicely.
test.lint(
    fails=True,
    verilator_flags2=[
        '--hierarchical-xmr-bind', 'blockOnly',  # needs block,port,path
    ],
    expect_filename=test.golden_filename)  # yapf:disable

test.passes()
