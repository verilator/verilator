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
test.top_filename = "t/t_randomize_solver_fault.v"

if not test.have_solver:
    test.skip("No constraint solver installed")

test.compile(verilator_flags2=['+define+T_SOFT'])

# Conflicting softs: relaxation keeps one of them
test.execute()
test.file_grep(test.run_log_filename, r'NPASS=5 NSOFT=5')

# Dead first probe condemns the session; each call reinjects until disabled
logfile = test.obj_dir + "/vlt_sim_silent2.log"
test.execute(logfile=logfile,
             run_env='VERILATOR_SOLVER=' + test.t_dir +
             '/randomize_solver_tamper.py TAMPER=silent_at TAMPER_AT=2')
test.file_grep(logfile, r'randomization disabled')

# Dead re-add probe keeps the highest-priority soft; the call still succeeds
logfile = test.obj_dir + "/vlt_sim_silent3.log"
test.execute(logfile=logfile,
             run_env='VERILATOR_SOLVER=' + test.t_dir +
             '/randomize_solver_tamper.py TAMPER=silent_at TAMPER_AT=3')
test.file_grep(logfile, r'NPASS=3 NSOFT=3')

test.passes()
