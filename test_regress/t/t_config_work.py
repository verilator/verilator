#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2025 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('simulator')

test.compile(
    verilator_flags2=['--binary', '--work liba', 't/t_config_work__liba.v', '--work libb', 't/t_config_work__libb.v'])

test.execute()

# Sort so that 'initial' scheduling order is not relevant
test.files_identical_sorted(test.run_log_filename, test.golden_filename, is_logfile=True)

test.passes()
