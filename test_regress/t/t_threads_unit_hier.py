#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vltmt')
test.top_filename = "t/t_threads_unit.v"

test.clean_objs()

# Each tile is both a hierarchical block and a unit, but is not a unit in its own Verilation,
# where only its acc is. Unlike the metacomment, the control file also marks the tiles'
# wrappers in the parent.
test.compile(verilator_flags2=[
    "--stats", "--hierarchical", "+define+TEST_VLT", "+define+TEST_HIERARCHICAL", "-CFLAGS",
    "-DVL_THREADS_SERIAL_COST=0"
],
             threads=2)

test.execute()

test.file_grep(
    test.obj_dir + "/" + test.vm_prefix + "__hier.dir/" + test.vm_prefix + "__stats.txt",
    r'MTask graph, threads_unit groups\s+(\d+)', 11)
test.file_grep(test.obj_dir + "/Vtile/Vtile__stats.txt",
               r'MTask graph, threads_unit groups\s+(\d+)', 1)

test.passes()
