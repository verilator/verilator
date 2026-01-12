#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2025 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('simulator')

test.compile(make_top_shell=False,
             make_main=False,
             make_pli=True,
             verilator_flags2=["+define+VERILATOR_COMMENTS --binary --vpi", test.pli_filename],
             v_flags2=["+define+USE_VPI_NOT_DPI"])

test.execute(xrun_flags2=["+define+USE_VPI_NOT_DPI"], use_libvpi=True, check_finished=True)

test.passes()
