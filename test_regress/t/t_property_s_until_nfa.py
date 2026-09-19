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

test.compile(verilator_flags2=['--assert', '+define+TEST_PRE_NOTIMING'],
             fails=True,
             expect_filename='t/t_property_s_until_nfa_pre.out')
test.lint(verilator_flags2=['--assert', '--no-timing', '+define+TEST_PRE_NOTIMING'],
          fails=True,
          expect_filename='t/t_property_s_until_nfa_pre.out')
test.compile(verilator_flags2=['--assert', '+define+TEST_WIDTH_NOTIMING'],
             fails=True,
             expect_filename='t/t_property_s_until_nfa_width.out')
test.lint(verilator_flags2=['--assert', '--no-timing', '+define+TEST_WIDTH_NOTIMING'],
          fails=True,
          expect_filename='t/t_property_s_until_nfa_width.out')
test.compile(verilator_flags2=['--assert', '--no-stop-fail'])
test.execute(expect_filename=test.golden_filename)

test.passes()
