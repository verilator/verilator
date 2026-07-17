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

# Must elaborate cleanly. Before the fix this is a use-after-free in
# V3LinkDotIfaceCapture (see t_iface_typedef_bits_uaf.v): it aborts under
# --enable-dev-asan, and SIGSEGVs in a --debug build once the findOwnerModule
# address guard is removed.
test.lint()

test.passes()
