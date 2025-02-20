#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test module
#
# Copyright 2025 by Antmicro. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt')
test.top_filename = "t/t_trace_counter.v"
test.golden_filename = "t/t_trace_counter_saif.out"

test.compile(verilator_flags2=['--cc --trace-saif'])

test.execute()

test.saif_identical(test.trace_filename, test.golden_filename)

test.passes()
