#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2025 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt')

# Compile with --binary --vpi to exercise the VPI-aware generated main.
# Also compile a VPI shared library to be loaded at runtime via +verilator+vpi+.
test.compile(make_pli=True, verilator_flags2=["--binary --vpi --public-flat-rw"])

# Run the generated binary; load the VPI library via the +verilator+vpi+ plusarg.
# The VPI library's output (observed 'count' reaching MAX_TICKS, then end-of-sim) is
# checked against the golden .out file.
# Also pass a non-VPI plusarg (skipped by the loader's prefix check) and a bare
# +verilator+vpi+ with an empty payload (skipped by the empty-arg check), so both
# loader-skip branches are exercised alongside the real library load.
test.execute(all_run_flags=[
    "+othertest", "+verilator+vpi+", "+verilator+vpi+" + test.obj_dir + "/libvpi.so"
],
             check_finished=True,
             expect_filename=test.golden_filename)

test.passes()
