#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap
import lib_inst_name_common

test.scenarios('vlt_all')

# The top module instance of the library is named after --l2-name
lib_inst_name_common.run(test, verilator_flags2=["-fno-inline"], lib_flags2=["--l2-name", "w"])
