#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

# +verilator+seed+0 should pick a non-zero random seed at startup, expose it
# through $get_initial_random_seed(), and pick a different value across runs
# so independent invocations are not deterministic.

test.scenarios('vlt')

test.compile(verilator_flags2=['--binary'])

seeds = []
for i in range(3):
    logfile = test.obj_dir + "/seed_zero_run" + str(i) + ".log"
    test.execute(all_run_flags=['+verilator+seed+0'], logfile=logfile)
    match = test.file_grep(logfile, r'seed=([0-9]+)')
    if match is None:
        test.error("Could not parse 'seed=NNN' from " + logfile)
    seeds.append(int(match[0]))

if any(s == 0 for s in seeds):
    test.error("+verilator+seed+0 produced a zero seed: " + repr(seeds))

if len(set(seeds)) < 2:
    test.error("+verilator+seed+0 must vary across runs, got: " + repr(seeds))

test.passes()
