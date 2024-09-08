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

test.compile(v_flags2=["t/" + test.name + "_c.cpp"], verilator_flags2=['--vpi'])

test.execute(fails=True)

test.file_grep(test.run_log_filename, r'vpi_release_handle.*called on same object twice')

test.passes()
