#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import runpy

import vltest_bootstrap
from repcut_common import round_robin_partitioner

test.scenarios('vlt_all')
# Internal graph and lowering reports are opt-in.
test.verilator_flags += ['--repcut-dump-graph']
test.top_filename = "t/t_property_nfa_stop_error_limit_crossing.v"
test.golden_filename = "t/t_property_nfa_stop_error_limit_crossing.out"
test.verilator_flags += ['-frepcut', '--repcut-partitioner', round_robin_partitioner(test)]
runpy.run_path("t/t_property_nfa_stop_error_limit_crossing.py", globals())
