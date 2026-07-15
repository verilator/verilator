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

ordinary_modes = ('return', 'constructor', 'constructor_args', 'constructor_args_complete',
                  'constructor_arg_expr', 'exprstmt', 'method_chain', 'short_circuit')
modes = ordinary_modes + ('reduction_complete', 'sort_complete', 'reduction', 'reduction_nested',
                          'reduction_sibling', 'sort', 'sort_late')

test.compile(verilator_flags2=['--binary', '--timing'])
for mode in modes:
    test.execute(all_run_flags=[f'+MODE={mode}'], logfile=test.obj_dir + f'/sim_{mode}.log')

test.passes()
