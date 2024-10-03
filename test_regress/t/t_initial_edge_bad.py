#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

# This works with other vlt_alls, we we don't run it for them. It should
# fail with Verilator if --x-initial-edge is not specified.

import vltest_bootstrap

test.scenarios('vlt_all')
test.top_filename = "t/t_initial_edge.v"

test.compile()

test.execute(fails=True)

test.passes()
