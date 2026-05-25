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

logfile = test.obj_dir + "/t_logfile_error.log"

test.execute(all_run_flags=['+verilator+log+file+' + logfile], fails=True)

# $error checks
test.file_grep(logfile, r'Error: t_logfile_error.v:11: Assertion failed in top.top: This is a generated error!')

test.passes()
