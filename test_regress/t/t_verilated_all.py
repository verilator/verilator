#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2024 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vltmt')

if not os.path.exists(test.root + "/.git"):
    test.skip("Not in a git repository")

if not re.search(r'g\+\+|GCC|clang', test.cxx_version):
    test.skip("Compiler does not support -fno-exceptions")

test.compile(
    # Can't use --coverage and --savable together, or multiple trace formats, so cheat and compile inline
    verilator_flags2=[
        "--cc",
        "--coverage-toggle --coverage-line --coverage-user",
        "--trace-fst",  # Also adds -lz4 and the like
        "--vpi",
        ("--timing" if test.have_coroutines else "--no-timing -Wno-STMTDLY"),
        "--prof-exec",
        "--prof-pgo",
        # -fno-exceptions checks the runtime/generated code does not rely on exceptions
        "-CFLAGS -fno-exceptions",
        test.root + "/include/verilated_save.cpp",
        test.root + "/include/verilated_vcd_c.cpp",
        test.root + "/include/verilated_saif_c.cpp"
    ],
    threads=2)

test.execute(
    all_run_flags=[" +verilator+prof+exec+file+/dev/null", " +verilator+prof+vlt+file+/dev/null"])

hit = {}
for filename in (test.glob_some(test.root + "/include/*.cpp") +
                 test.glob_some(test.root + "/include/*.h")):
    filename = os.path.basename(filename)
    if test.verbose:
        print("NEED: " + filename)
    hit[filename] = False

for dfile in test.glob_some(test.obj_dir + "/*.d"):
    wholefile = test.file_contents(dfile)
    for filename in wholefile.split():
        filename = os.path.basename(filename)
        if test.verbose:
            print("USED: " + filename)
        hit[filename] = True

for filename in sorted(hit.keys()):
    if hit[filename]:
        continue
    if re.search(r'_sc', filename):  # SystemC files are not built by this test
        continue
    if re.search(r'_timing', filename) and not test.have_coroutines:
        continue
    test.error("Include file not covered by t_verilated_all test: ", filename)

test.passes()
