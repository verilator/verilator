#!/usr/bin/env python3
# DESCRIPTION: Verilator: Regression test for min_uaf_repro_real

import vltest_bootstrap

test.scenarios('simulator')
test.top_filename = "t/t_min_uaf_repro_real.sv"

test.compile(verilator_flags2=['--binary', '--timing', '--debug'])

test.execute()

test.passes()
