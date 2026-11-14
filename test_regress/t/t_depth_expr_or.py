#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Dave Keeshan
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt')

if test.have_dev_gcov:
    test.skip("Too slow with code coverage")

test.timeout(60)

# The wrapper raises the stack unless this is set. A flat OR of 12000
# inputs segfaults in WidthVisitor at the default 8MB limit.
# Elaboration only, same as t_opt_const_big_or_tree.
test.compile(verilator_make_gmake=False, verilator_flags2=["--no-unlimited-stack"])

test.passes()
