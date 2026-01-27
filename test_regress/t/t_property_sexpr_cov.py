#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2025 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('simulator')

test.compile(timing_loop=True, verilator_flags2=['--assert', '--timing', '--coverage-user'])

test.execute(expect_filename=test.golden_filename)
test.files_identical(test.obj_dir + "/coverage.dat", "t/t_property_sexpr_cov.dat.out")

test.passes()
