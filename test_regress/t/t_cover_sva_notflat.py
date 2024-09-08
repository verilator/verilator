#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('simulator')

test.compile(verilator_flags2=['--assert --cc --coverage-user'])

test.execute()

#if test.nc: ... # See t_assert_cover.py for NC version

# Allow old SystemC::Coverage format dump, or new binary dump
# Check that the hierarchy doesn't include __PVT__
# Otherwise our coverage reports would look really ugly
if test.vlt_all:
    test.file_grep(test.coverage_filename, r'(top\.t\.sub.*.cyc_eq_5)')

test.passes()
