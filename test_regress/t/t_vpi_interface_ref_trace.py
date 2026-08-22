#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

# As t_vpi_interface_ref, but with tracing also enabled. Trace and VPI both
# consume the AstIntfRef nodes that describe interface references, so check
# they do not interfere.
test.scenarios('vlt_all')
test.top_filename = "t/t_vpi_interface_ref.v"
test.pli_filename = "t/t_vpi_interface_ref.cpp"

test.compile(make_top_shell=False,
             make_main=False,
             make_pli=True,
             verilator_flags2=[
                 "--exe --vpi --timing --no-l2name --public-flat-rw --trace-vcd",
                 test.pli_filename, "t/TestVpiMain.cpp"
             ])

test.execute(use_libvpi=True)

test.passes()
