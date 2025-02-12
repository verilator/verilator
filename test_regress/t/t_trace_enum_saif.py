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
test.top_filename = "t/t_trace_enum.v"

test.compile(verilator_flags2=['--cc --trace-saif --output-split-ctrace 1'])

test.execute()

test.saif_identical(test.trace_filename, test.golden_filename)

# Five $attrbegin expected:
# - state_t declaration
# - t.v_enumed
# - t.sink.state
# - other_state_t declaration
# - t.v_other_enumed
test.file_grep_count(test.golden_filename, r'attrbegin', 5)

test.passes()
