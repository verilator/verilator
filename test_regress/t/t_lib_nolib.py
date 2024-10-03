#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt_all', 'xsim')
test.top_filename = "t/t_lib_prot.v"

if test.benchmark:
    test.sim_time = test.benchmark * 100

trace_opt = ("" if re.search(r'--no-trace', ' '.join(test.driver_verilator_flags)) else "-trace")

# Tests the same code as t_lib_prot.py but without --protect-lib
test.compile(verilator_flags2=['--no-timing', trace_opt, "t/t_lib_prot_secret.v"],
             xsim_flags2=["t/t_lib_prot_secret.v"])

test.execute()

if test.vlt and test.trace:
    # We can see the ports of the secret module
    test.file_grep(test.trace_filename, r'accum_in')
    # and we can see what's inside (because we didn't use --protect-lib)
    test.file_grep(test.trace_filename, r'secret_')

test.passes()
