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

test.top_filename = 't/t_covergroup_wildcard_max_bins.v'

test.compile(verilator_flags2=['--coverage', '--coverage-max-bins 4', '-Wno-COVERIGN'])

# An illegal value of the sized array of more ranges of values than the limit
test.execute(fails=True,
             check_finished=False,
             all_run_flags=['+illegal=3'],
             expect_filename=test.golden_filename)

test.passes()
