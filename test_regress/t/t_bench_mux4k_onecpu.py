#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('simulator')
test.top_filename = "t/t_bench_mux4k.v"

test.compile(v_flags2=["--stats", test.wno_unopthreads_for_few_cores])

# WSL2 gives a warning and we must skip the test:
#  "physcpubind: 0 1 2 3 ...\n No NUMA support available on this system."
nout = test.run_capture("numactl --show", check=False)

if not nout or not re.search(r'cpu', nout) or re.search(r'No NUMA support available', nout,
                                                        re.IGNORECASE):
    test.skip("No numactl available")

test.execute(run_env='numactl -m 0 -C 0,0,0,0,0,0,0,0')

test.passes()
