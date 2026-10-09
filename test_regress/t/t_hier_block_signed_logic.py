#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2024 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('simulator')

test.clean_objs()
test.compile(verilator_flags2=['--stats', '--hierarchical'])

test.execute()

test.file_grep(test.obj_dir + "/Vsub/sub.sv", r'^module\s+(\S+)\s+', "sub")
# Whole-vector transfers can hide a reversed range in the wrapper declaration.
test.file_grep(test.obj_dir + "/Vsub/sub.sv", r'input logic\s+\[2:8\]\s+ascending_in')
test.file_grep(test.obj_dir + "/Vsub/sub.sv", r'output logic\s+\[2:8\]\s+ascending_out')
test.file_grep(test.obj_dir + "/Vsub/sub.sv", r'input logic\s+\[10:4\]\s+descending_in')
test.file_grep(test.obj_dir + "/Vsub/sub.sv", r'output logic\s+\[10:4\]\s+descending_out')
test.file_grep(test.stats, r'HierBlock,\s+Hierarchical blocks\s+(\d+)', 1)

test.passes()
