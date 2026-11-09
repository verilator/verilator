#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import os
import signal
import subprocess

import vltest_bootstrap

test.scenarios('vlt')
test.top_filename = "t/t_EXAMPLE.v"

binary = os.path.join(os.environ['VERILATOR_ROOT'], "bin",
                      os.environ.get("VERILATOR_BIN", "verilator_bin"))
cmd = [binary, "--lint-only", "-Mdir", test.obj_dir, "--debugi", "3", "--verilate-jobs", "2",
       "--debug-self-test", "--debug-fatalsrc-worker", test.top_filename]
with open(test.compile_log_filename, 'w', encoding='utf8') as output:
    try:
        result = subprocess.run(cmd, stdout=output, stderr=subprocess.STDOUT, timeout=30,
                                check=False)
    except subprocess.TimeoutExpired:
        test.error("Worker fatal did not terminate within 30 seconds")
    else:
        if result.returncode not in (-signal.SIGABRT, 128 + signal.SIGABRT):
            test.error("Worker fatal did not terminate with SIGABRT")
test.file_grep(test.compile_log_filename,
               r'%Error: Internal Error: .*: --debug-fatalsrc-worker')
test.file_grep(test.compile_log_filename, r'Aborting since under --debug')
test.file_grep_not(test.compile_log_filename, r'Resource deadlock avoided|std::system_error')

test.passes()
