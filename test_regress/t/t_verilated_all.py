#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vltmt')

root = ".."

if not os.path.exists(root + "/.git"):
    test.skip("Not in a git repository")

test.compile(
    # Can't use --coverage and --savable together, so cheat and compile inline
    verilator_flags2=[
        "--cc", "--coverage-toggle --coverage-line --coverage-user",
        "--trace --vpi ", "--trace-threads 1",
        ("--timing" if test.have_coroutines else "--no-timing -Wno-STMTDLY"), "--prof-exec",
        "--prof-pgo", root + "/include/verilated_save.cpp"
    ],
    threads=2)

test.execute(
    all_run_flags=[" +verilator+prof+exec+file+/dev/null", " +verilator+prof+vlt+file+/dev/null"])

hit = {}
for filename in (test.glob_some(root + "/include/*.cpp") + test.glob_some(root + "/include/*.h")):
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
    if (not hit[filename] and not re.search(r'_sc', filename) and not re.search(r'_fst', filename)
            and not re.search(r'_saif', filename)
            and not re.search(r'_thread', filename)
            and (not re.search(r'_timing', filename) or test.have_coroutines)):
        test.error("Include file not covered by t_verilated_all test: ", filename)

test.passes()
