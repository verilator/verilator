#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2024 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt')

# Verify that the SV wrapper retains the original inout port.
test.compile(verilator_flags2=["--protect-lib", "secret", "--protect-key", "secret-key"],
             verilator_make_gmake=False,
             make_main=False)

test.file_grep(test.obj_dir + "/secret.sv", r'inout logic z')

test.passes()
