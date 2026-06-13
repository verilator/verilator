#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2024 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

# Note: This test is historical for the isolate_assignments attribute, which
# was deprecated and has no effect today. This test ensures it still parses
# in SystemVerilog and Verilator control files for backward compatibility.

test.scenarios('vlt')
test.top_filename = "t/t_unopt_combo.v"

test.compile(verilator_flags2=["+define+ISOLATE"])

test.execute()

test.passes()
