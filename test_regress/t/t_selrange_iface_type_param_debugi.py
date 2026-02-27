#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

# Debug-variant of t_selrange_iface_type_param: enables IfaceCapture debug
# output and verifies type-parameter capture and propagation messages.

import vltest_bootstrap

test.scenarios('vlt')

test.top_filename = "t/t_selrange_iface_type_param.v"

test.compile(
    v_flags2=[
        "--binary --debug --debugi 0 --debugi-V3LinkDotIfaceCapture 9"
    ])

test.file_grep(test.compile_log_filename,
               r"propagateClone:")
test.file_grep(test.compile_log_filename,
               r"iface capture add:")
test.file_grep(test.compile_log_filename,
               r"iface capture dumpEntries:")

test.execute()

test.passes()
