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

if test.have_coroutines:
    test.run(cmd=[os.environ["VERILATOR_ROOT"] + "/bin/verilator --get-supported COROUTINES"],
             expect="""1
""",
             logfile=test.obj_dir + "/vlt_coroutines.log",
             verilator_run=True)

if test.have_sc:
    test.run(cmd=[os.environ["VERILATOR_ROOT"] + "/bin/verilator --get-supported SYSTEMC"],
             expect="""1
""",
             logfile=test.obj_dir + "/vlt_systemc.log",
             verilator_run=True)

test.run(cmd=[os.environ["VERILATOR_ROOT"] + "/bin/verilator --get-supported DOES_NOT_EXIST"],
         expect='',
         logfile=test.obj_dir + "/vlt_does_not_exist.log",
         verilator_run=True)

test.passes()
