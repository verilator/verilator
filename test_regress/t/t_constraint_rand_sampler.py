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


def check_default(name, flags, run_env=''):
    # Verilator samples: results vary and it sends no seed
    log = run(name, flags + ['+check_varied'], run_env)
    test.file_grep(log, r'; sampler: default')
    test.file_grep_not(log, r'; sampler: solver')
    test.file_grep_not(log, r':random-seed')


def check_solver(name, flags, run_env=''):
    # The solver samples: its model is the result, seeded per query. Whether
    # results vary depends on the solver, so that is not checked.
    log = run(name, flags, run_env)
    test.file_grep(log, r'; sampler: solver')
    test.file_grep_not(log, r'; sampler: default')
    # Seeding and a single solve per query are what this sampler promises, and
    # results are legal either way, so only the transcript can show them
    with open(log, 'r', encoding='utf8') as fh:
        queries = fh.read().split('(set-option :produce-models true)')[1:]
    # One solver call per query: no follow-up sampling rounds
    multi = [q for q in queries if q.count('(check-sat') != 1]
    if multi:
        test.error("Expected one check-sat per query, " + str(len(multi)) + " queries had more")
    # Only the two randomize(null) checks are unseeded, as they are not random
    unseeded = [q for q in queries if ':random-seed' not in q]
    if len(unseeded) != 2:
        test.error("Expected 2 unseeded randomize(null) queries, got " + str(len(unseeded)))


if CONFIGURED == "solver":
    check_solver("default", [])
else:
    check_default("default", [])

check_default("default_name", ['+verilator+rand+sampler+default'])
check_solver("solver", ['+verilator+rand+sampler+solver'])

# $VERILATOR_RAND_SAMPLER when the model runs sets the default; plusargs override it
check_solver("env_solver", [], run_env='VERILATOR_RAND_SAMPLER=solver')
check_default("env_default", [], run_env='VERILATOR_RAND_SAMPLER=default')
check_default("env_plusarg", ['+verilator+rand+sampler+default'],
              run_env='VERILATOR_RAND_SAMPLER=solver')

test.passes()
