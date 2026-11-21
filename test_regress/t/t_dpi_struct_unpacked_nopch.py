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
test.top_filename = "t/t_dpi_struct_unpacked.v"
test.pli_filename = "t/t_dpi_struct_unpacked.cpp"

# As t_dpi_struct_unpacked, but without the forced PCH include, as in CMake builds,
# so __Dpi.cpp itself must declare the DPI exports as exports
test.compile(v_flags2=[test.pli_filename],
             verilator_flags2=[
                 "-CFLAGS -Werror=attributes",
                 "-CFLAGS \"'-DVL_API_EXPORT=__attribute__((visibility(\\\"default\\\")))'\"",
                 "-CFLAGS \"'-DVL_API_IMPORT=__attribute__((visibility(\\\"hidden\\\")))'\""
             ],
             make_flags=["VK_PCH_I_FAST="])

test.execute()

test.passes()
