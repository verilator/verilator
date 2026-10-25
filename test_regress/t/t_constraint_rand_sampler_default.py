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
test.top_filename = "t/t_constraint_rand_sampler.v"

if not test.have_solver:
    test.skip("No constraint solver installed")

# $VERILATOR_RAND_SAMPLER when Verilator runs (as for a --with-rand-sampler build)
# is compiled into the model as its default sampler
test.setenv('VERILATOR_RAND_SAMPLER', 'solver')

test.run(cmd=[os.environ["VERILATOR_ROOT"] + "/bin/verilator --getenv VERILATOR_RAND_SAMPLER"],
         logfile=test.obj_dir + "/getenv.log",
         verilator_run=True)
test.file_grep(test.obj_dir + "/getenv.log", r'^solver$')

test.compile()

test.file_grep(test.obj_dir + "/" + test.vm_prefix + ".mk",
               r"-DVM_RAND_SAMPLER_DEFAULT='\"solver\"'")

# The model, run without the variable, keeps the default it was built with
os.environ.pop('VERILATOR_RAND_SAMPLER', None)
log = test.obj_dir + "/solver.log"
test.execute(all_run_flags=['+verilator+solver+file+' + log])
test.file_grep(log, r'; sampler: solver')

test.passes()
