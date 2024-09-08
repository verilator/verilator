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

test.compile(
    # For Verilator, all PARAMs at all levels are overridden
    # Error if parameter not found
    #verilator_flags2 = ['-GPARAM=10 -Gtop.t.x.HIER=20'],  # HIER would error
    verilator_flags2=['-GPARAM=10'],
    # For NC, always implies a hierarchy, only HIER will be set
    # Warns if sets nothing
    nc_flags2=['+defparam+PARAM=10 +defparam+top.t.x.HIER=20'],
    # For VCS, all PARAMs at all levels are overridden. Hierarchy not allowed.
    # Informational on all overrides
    vcs_flags2=['-pvalue+PARAM=10 -px.HIER=20'],
    # For icarus -P without hierarchy does nothing, only can ref into top
    iv_flags2=['-PPARAM=10', '-Ptop.HIER=30', '-Ptop.t.x.HIER=20'])

test.execute()

test.passes()
