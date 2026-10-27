#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('simulator')

# TODO: The virtual interface written through in always_comb is reported as written there
test.compile(verilator_flags2=[
    "--binary",
    "-Wno-MULTIDRIVEN",
    # Dev coverage of V3EmitV
    "--dumpi-tree 3",
    "--debug-emitv"
])

test.execute()

test.passes()
