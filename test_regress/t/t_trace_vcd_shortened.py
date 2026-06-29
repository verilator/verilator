#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

import os
import platform

test.scenarios('vlt')

if platform.machine().lower() not in ("amd64", "x86_64"):
    test.skip("Test requires x86-64 AVX2/LZCNT")

if os.path.exists("/proc/cpuinfo"):
    with open("/proc/cpuinfo", encoding="utf-8") as fh:
        cpuinfo = " " + fh.read().lower() + " "
    if " avx2 " not in cpuinfo or (" lzcnt " not in cpuinfo and " abm " not in cpuinfo):
        test.skip("Test requires x86-64 AVX2/LZCNT")

test.compile(verilator_flags2=[
    "--binary", "--trace-vcd", "-CFLAGS", "\"-mavx2 -mlzcnt\""
])

test.execute()

code = r"[!-~]+"

test.file_grep(test.trace_filename, rf"^b0 {code}$")
test.file_grep(test.trace_filename, rf"^b10 {code}$")
test.file_grep(test.trace_filename, rf"^b1 {code}$")
test.file_grep(test.trace_filename, rf"^b1000000000000000 {code}$")
test.file_grep(test.trace_filename, rf"^b10100101 {code}$")
test.file_grep(test.trace_filename, rf"^b1{'0' * 63} {code}$")
test.file_grep(test.trace_filename, rf"^b1{'0' * 32} {code}$")
test.file_grep(test.trace_filename, rf"^b1{'0' * 65} {code}$")

test.file_grep_not(test.trace_filename, rf"^b0[01]+ {code}$")

test.passes()
