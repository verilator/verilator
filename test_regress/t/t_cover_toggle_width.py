#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt')
test.top_filename = "t/t_cover_toggle.v"

test.compile(verilator_flags2=['--cc --coverage-toggle --coverage-max-width 1025'])

test.execute()

test.file_grep(test.obj_dir + "/coverage.dat", "largeish")

test.passes()
