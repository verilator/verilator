#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt')
test.top_filename = "t/t_flag_j_hier.v"

test.compile(verilator_flags2=['--hierarchical --build --build-jobs 2'])

# Each hierarchical block must be Verilated once, even with a parallel build
test.file_grep_count(test.compile_log_filename, r'-f \S*Vs__hierMkArgs\.f', 1)

test.passes()
