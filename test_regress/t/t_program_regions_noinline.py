#!/usr/bin/env python3
# DESCRIPTION: Verilator: Program event region scheduling without module inlining
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('simulator')
test.top_filename = "t/t_program_regions.v"

test.compile(verilator_flags2=["--binary", "-fno-inline"], threads=2 if test.vltmt else 1)

test.execute()

test.passes()
