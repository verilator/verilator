#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('simulator')

test.sim_time = 2700

test.compile(timing_loop=True,
             verilator_flags2=['--assert', '--timing', '--coverage-user', '--dumpi-graph', '6'])

# Keep this multiplicity-free cover-sequence ring bit-packed to avoid 32x storage.
if test.vlt_all:
    headers = test.glob_some(test.obj_dir + "/" + test.vm_prefix + "*.h")
    test.file_grep_any(headers, r'VlWide<32>.*/\*1023:0\*/.*__Vnfa___0__d2_ring')

test.execute()

test.passes()
