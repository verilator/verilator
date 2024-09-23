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

test.setenv('FOOBARTEST', "gotit")

test.run(cmd=[os.environ["VERILATOR_ROOT"] + "/bin/verilator --getenv FOOBARTEST"],
         logfile=test.compile_log_filename,
         verilator_run=True)

test.file_grep(test.compile_log_filename, r'gotit')

for var in [
        'MAKE', 'PERL', 'PYTHON3', 'SYSTEMC', 'SYSTEMC_ARCH', 'SYSTEMC_LIBDIR', 'VERILATOR_ROOT'
]:
    test.run(cmd=[os.environ["VERILATOR_ROOT"] + "/bin/verilator", "--getenv", var],
             logfile=test.obj_dir + "/simx.log",
             verilator_run=True)

test.passes()
