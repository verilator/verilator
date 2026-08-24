#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap
import trace_complex_common

test.scenarios('vlt_all')

# Run time model descriptor tables in chunks of 2 rows, so all are split
trace_complex_common.run(test, verilator_flags2=["--output-split-rtmd 1"])

# Make sure they were split
for table in ("DataType", "Global", "Hier", "SignalType"):
    test.glob_some(test.obj_dir + "/" + test.vm_prefix + "__Rtmd" + table + "Table__1*.cpp")
