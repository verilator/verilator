#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2025 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('dist')

test.passes()

test.timeout(1)

# Check whether the soft limit is set to 1s
test.run(cmd=["bash", "-c", "\"[ '$(ulimit -St)' -eq 1 ] || exit 1\""])

# Set the hard limit to 2s (in case soft limit fails) and run a command which spins until signalled
test.run(cmd=["bash", "-c", "\"trap 'exit 0' SIGXCPU; ulimit -Ht 2; while :; do :; done\""])

test.passes()
