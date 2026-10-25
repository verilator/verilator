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

if not test.have_solver:
    test.skip("No constraint solver installed")

# Default as Verilator was configured (--with-rand-sampler)
os.environ.pop('VERILATOR_RAND_SAMPLER', None)
CONFIGURED = test.run_capture(os.environ["VERILATOR_ROOT"] +
                              "/bin/verilator --getenv VERILATOR_RAND_SAMPLER").strip()

test.compile()


def run(name, flags, run_env=''):
    log = test.obj_dir + "/solver_" + name + ".log"
    test.execute(logfile=test.obj_dir + "/sim_" + name + ".log",
                 all_run_flags=flags + ['+verilator+solver+file+' + log],
                 run_env=run_env)
    return log


def check_default(log):
    # Verilator samples: UniGen2 cells (push, XOR hashes), diversity pins
    # (check-sat-assuming) and XOR rounds, and sends no seed
    test.file_grep(log, r'\(push 1\)')
    test.file_grep(log, r'\(check-sat-assuming')
    test.file_grep(log, r'\(bvxor')
    test.file_grep_not(log, r':random-seed')


def check_solver(log):
    # The solver samples: its model is the result, seeded per query
    test.file_grep(log, r'\(set-option :random-seed \d+\)')
    test.file_grep_not(log, r'\(push')
    test.file_grep_not(log, r'\(check-sat-assuming')
    test.file_grep_not(log, r'\(bvxor')
    test.file_grep_not(log, r':produce-unsat-assumptions')
    # Only the two randomize(null) checks are unseeded, as they are not random
    with open(log, 'r', encoding='utf8') as fh:
        queries = fh.read().split('(set-option :produce-models true)')[1:]
    # One solver call per query: no follow-up sampling rounds
    multi = [q for q in queries if q.count('(check-sat') != 1]
    if multi:
        test.error("Expected one check-sat per query, " + str(len(multi)) + " queries had more")
    unseeded = [q for q in queries if ':random-seed' not in q]
    if len(unseeded) != 2:
        test.error("Expected 2 unseeded randomize(null) queries, got " + str(len(unseeded)))


if CONFIGURED == "solver":
    check_solver(run("default", []))
else:
    check_default(run("default", []))

check_default(run("default_name", ['+verilator+rand+sampler+default']))
check_solver(run("solver", ['+verilator+rand+sampler+solver']))

# $VERILATOR_RAND_SAMPLER when the model runs sets the default; plusargs override it
check_solver(run("env_solver", [], run_env='VERILATOR_RAND_SAMPLER=solver'))
check_default(run("env_default", [], run_env='VERILATOR_RAND_SAMPLER=default'))
check_default(
    run("env_plusarg", ['+verilator+rand+sampler+default'],
        run_env='VERILATOR_RAND_SAMPLER=solver'))

test.execute(all_run_flags=['+verilator+rand+sampler+0'],
             fails=True,
             logfile=test.obj_dir + "/sim_bad.log")
test.file_grep(test.obj_dir + "/sim_bad.log",
               r"Argument '\+verilator\+rand\+sampler\+' must be 'default' or 'solver'")

test.execute(run_env='VERILATOR_RAND_SAMPLER=fast',
             fails=True,
             logfile=test.obj_dir + "/sim_bad_env.log")
test.file_grep(test.obj_dir + "/sim_bad_env.log",
               r"VERILATOR_RAND_SAMPLER must be 'default' or 'solver': fast")

test.passes()
