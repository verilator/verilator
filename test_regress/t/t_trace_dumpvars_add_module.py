#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 by Marco Bartoli.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt')

test.compile(verilator_flags2=['--binary --timing --trace-vcd'])

test.execute()

test.vcd_identical(test.obj_dir + '/simx0.vcd', test.t_dir + '/t_trace_dumpvars_add_module_0.out')
test.vcd_identical(test.obj_dir + '/simx1.vcd', test.t_dir + '/t_trace_dumpvars_add_module_1.out')

test.passes()
