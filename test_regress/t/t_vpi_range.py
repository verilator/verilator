#!/usr/bin/env python3

import vltest_bootstrap

test.scenarios('simulator')
test.pli_filename = "t/t_vpi_range.cpp"
test.top_filename = "t/t_vpi_range.v"

test.compile(make_top_shell=False,
             make_main=False,
             verilator_flags2=['--exe', '-Wno-ASCRANGE', '--vpi', '--public-flat-rw', test.pli_filename])

test.execute()

test.passes()
