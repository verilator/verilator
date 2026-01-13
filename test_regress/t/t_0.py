#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2025 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('simulator')

test.compile(verilator_flags2=[
    '--binary', '-j 0', '--Wno-WIDTH', '-Wno-MISINDENT', '-Wno-REALCVT', '-Wno-CASTCONST',
    '-Wno-SIDEEFFECT', '--Wno-CONSTRAINTIGN', '--Wno-COVERIGN', '--Wno-SYMRSVDWORD',
    '--Wno-CASEINCOMPLETE', '--Wno-IGNOREDRETURN', '--Wno-DECLFILENAME', '--Wno-RANDC',
    '--Wno-UNUSED', '--Wno-UNDRIVEN', '--Wno-VARHIDDEN', '--Wno-EOFNEWLINE', '--Wno-IMPORTSTAR',
    '--Wno-MISINDENT', '--Wno-MULTITOP', '--Wno-NONSTD', '--Wno-SHORTREAL', '--timescale','1ns/1ns',
    '--vpi', 't/t_0_uvm_dpi/uvm_dpi.cc'
])

test.execute(all_run_flags=['+UVM_TESTNAME=test', '+UVM_NO_RELNOTES', '+UVM_CONFIG_DB_TRACE', '+UVM_OBJECTION_TRACE', '+UVM_PHASE_TRACE'])

test.file_grep_not(test.run_log_filename, r'UVM_FATAL\s*:\s*[^0\s]')

test.passes()
