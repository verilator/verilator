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

test.compile(
    make_top_shell=False,
    make_main=False,
    verilator_flags2=["--exe --vpi --vpi-lazy-public-rw --no-l2name --stats", test.pli_filename])

test.execute()

# The interface member `val` has three instances with differing per-instance
# drivers, so all three are retained rather than reconstructed by one shared func.
test.file_grep(test.stats, r'VPI, lazy cross-scope retained\s+(\d+)', 3)
# The class-internal `derived` cone is identical across instances: still lazy.
test.file_grep(test.obj_dir + "/" + test.vm_prefix + "__Syms.h", r'__Vlazy_reconstruct')

test.passes()
