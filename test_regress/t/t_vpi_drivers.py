#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

# Not vltmt, whose threads may run the design's DPI calls into VPI off the main thread
test.scenarios('vlt', 'ms')

test.compile(make_top_shell=False,
             make_pli=True,
             verilator_flags2=["--binary --vpi --public-flat-rw --no-l2name", test.pli_filename])

# The DPI imports live in the VPI library; t_xq is called from a VPI callback
test.execute(use_libvpi=True,
             check_finished=True,
             ms_run_flags=test.ms_run_flags +
             ["-sv_lib", test.obj_dir + "/libvpi", "-dpioutoftheblue", "1"])

test.passes()
