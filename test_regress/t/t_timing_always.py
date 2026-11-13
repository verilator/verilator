#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2024 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('simulator')

test.compile(verilator_flags2=["--binary"])

if test.vlt_all:
    # Timing without DPI must not pull in the DPI worker implementation.
    test.file_grep_not(test.obj_dir + "/" + test.vm_prefix + "_classes.mk", r'verilated_dpi_call')

test.execute()

test.passes()
