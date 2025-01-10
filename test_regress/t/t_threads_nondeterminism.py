#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vltmt')
test.top_filename = "t/t_threads_counter.v"

test.compile(verilator_flags2=['--cc --debug-nondeterminism --no-skip-identical'], threads=2)

test.execute()

test.file_grep(test.compile_log_filename, r'Hash of shape')

test.passes()
