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

test.compile(verilator_flags2=['+define+T_PHASED'])

# Error instead of the phase get-value reply fails that call only
logfile = test.obj_dir + "/vlt_sim_err_reply.log"
test.execute(logfile=logfile,
             run_env='VERILATOR_SOLVER=' + test.t_dir +
             '/randomize_solver_tamper.py TAMPER=err_reply TAMPER_AT=1')
test.file_grep(logfile, r'NPASS=4')
test.file_grep(logfile, r'All Finished')

# Dead phase check-sat condemns the session; each call reinjects until disabled
logfile = test.obj_dir + "/vlt_sim_silent_at.log"
test.execute(logfile=logfile,
             run_env='VERILATOR_SOLVER=' + test.t_dir +
             '/randomize_solver_tamper.py TAMPER=silent_at TAMPER_AT=2')
test.file_grep(logfile, r'randomization disabled')
test.file_grep(logfile, r'All Finished')

test.passes()
