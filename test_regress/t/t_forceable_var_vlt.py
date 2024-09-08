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
test.pli_filename = "t/t_forceable_var.cpp"
test.top_filename = "t/t_forceable_var.v"

test.compile(make_top_shell=False,
             make_main=False,
             verilator_flags2=['--exe', test.pli_filename, test.t_dir + "/t_forceable_var.vlt"])

test.execute()

test.passes()
