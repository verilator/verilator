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
test.top_filename = "t/t_trace_complex.v"

test.compile(verilator_flags2=['--cc --trace-vcd --trace-structs --no-trace-params'])

test.execute()

test.file_grep(test.trace_filename, r' v_strp ')
test.file_grep(test.trace_filename, r' v_strp_strp ')
test.file_grep(test.trace_filename, r' v_arrp ')
test.file_grep_not(test.trace_filename, r' v_arrp_arrp ')
test.file_grep_not(test.trace_filename, r' v_arrp_strp ')
test.file_grep(test.trace_filename, r' v_arru\[')
test.file_grep(test.trace_filename, r' v_arru_arru\[')
test.file_grep(test.trace_filename, r' v_arru_arrp\[')
test.file_grep(test.trace_filename, r' v_arru_strp\[')

test.vcd_identical(test.trace_filename, test.golden_filename)

test.passes()
