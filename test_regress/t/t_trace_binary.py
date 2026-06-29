#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2024 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

import os
import platform

test.scenarios('vlt')

verilator_flags2 = ['--binary --trace']
if platform.machine().lower() in ("amd64", "x86_64") and os.path.exists("/proc/cpuinfo"):
    with open("/proc/cpuinfo", encoding="utf-8") as fh:
        cpuinfo = " " + fh.read().lower() + " "
    if " avx2 " in cpuinfo and (" lzcnt " in cpuinfo or " abm " in cpuinfo):
        verilator_flags2 += ["-CFLAGS", "\"-mavx2 -mlzcnt\""]

test.compile(
    verilator_flags=[  # Custom as don't want -cc
        "-Mdir " + test.obj_dir, "--debug-check"
    ],
    verilator_flags2=verilator_flags2)

test.execute()

test.vcd_identical(test.trace_filename, test.golden_filename)

test.passes()
