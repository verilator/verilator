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
test.top_filename = 't/t_finish_container_sort.v'

receivers = ('queue', 'dynamic', 'fixed')
directions = ('sort', 'rsort')
triggers = ('first', 'late', 'complete')
modes = tuple(f'{receiver}_{direction}_{trigger}' for receiver in receivers
              for direction in directions for trigger in triggers)


def execute_modes():
    for mode in modes:
        test.execute(all_run_flags=[f'+MODE={mode}'], logfile=test.obj_dir + f'/sim_{mode}.log')


test.compile(verilator_flags2=['--binary'])
execute_modes()

test.passes()
