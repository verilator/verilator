#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

# As t_vpi_interface_ref_scopes, but without --public-flat-rw, so nothing is
# VPI visible and no scope reaches the scope table. Interface references to a
# scope that is not in the table must be dropped, leaving an empty dump.
test.scenarios("vlt")
test.top_filename = "t/t_vpi_interface_ref_scopes.v"

test.compile(verilator_flags2=["--binary", "--vpi"])

test.execute()

test.files_identical(test.run_log_filename, test.golden_filename, is_logfile=True, strip_hex=True)

test.passes()
