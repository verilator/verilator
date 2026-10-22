#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt_all')
test.top_filename = test.t_dir + '/t_hier_block_libdir_pkg.v'
test.clean_objs()

test.compile(verilator_make_cmake=True,
             verilator_make_gmake=False,
             verilator_flags2=[
                 '--hierarchical', test.t_dir + '/t_hier_block_libdir_pkg/hier.vlt', '-y',
                 test.t_dir + '/t_hier_block_libdir_pkg',
                 test.t_dir + '/t_hier_block_libdir_pkg/pkg.vh'
             ],
             threads=(2 if test.vltmt else 1))

test.execute()

test.passes()
