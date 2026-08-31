#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt')

test.compile(verilator_flags2=['--binary'])
test.execute()

mem_usage_mb = int(test.file_grep(test.run_log_filename, r'allocated +(\d+) MB')[0])

if mem_usage_mb > 128 and not test.have_dev_asan:  # ASAN inflates memory usage by retaining freed stuff
    test.error('Consumed over 128MB memory')

test.passes()
