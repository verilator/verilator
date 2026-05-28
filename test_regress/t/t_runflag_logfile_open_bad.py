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

test.compile()

badfile = "/does-not-exist/badfile.log"
logfile = test.obj_dir + "/logfile.log"

log_flags = '+verilator+log+file+' + badfile
test.execute(all_run_flags=[log_flags, ">", logfile, "2>&1"], fails=True)

test.files_identical(logfile, test.golden_filename)

test.passes()
