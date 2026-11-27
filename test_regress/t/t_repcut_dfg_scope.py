#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026-2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

from pathlib import Path

import vltest_bootstrap
from repcut_common import round_robin_partitioner

test.scenarios('vltmt')
test.compile(make_main=False,
             threads=2,
             verilator_flags2=[
                 '-frepcut', '--output-split-cfuncs', '32', '--repcut-dump-graph',
                 '--repcut-partitioner',
                 round_robin_partitioner(test), '--exe',
                 str(Path(test.pli_filename).resolve())
             ])
test.execute()
test.passes()
