#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import os
import stat
import vltest_bootstrap

test.scenarios('vlt')

test.compile()

logfile = test.obj_dir + "/logfile.log"
capturefile = test.obj_dir + "/capture.log"

# Create the logfile
with open(logfile, 'w', encoding='utf8') as f:
    f.write("Read-only logfile\n")
# Change permission to read only so execute() fail when creating the logfile
os.chmod(logfile, stat.S_IREAD)

log_flags = '+verilator+log+file+' + logfile
test.execute(all_run_flags=[log_flags, ">", capturefile, "2>&1"], fails=True)

# Set read + write so test does not fail next time it is run
os.chmod(logfile, stat.S_IREAD | stat.S_IWRITE)

test.file_grep(capturefile, r"logfile.log cannot be created")
test.file_grep_not(capturefile, r"We should not see this message")

test.passes()
