#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2024 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import os
import re

import vltest_bootstrap

test.priority(100)
test.scenarios('vltmt')
test.top_filename = "t/t_EXAMPLE.v"

test.lint(threads=2, v_flags=["--verilate-jobs 2 --debug-self-test"])

# Use the configured DBG compile/link recipes without changing compiler objects.
objects = [
    os.path.abspath(obj) for obj in test.glob_some(test.root + "/src/obj_dbg/*.o")
    if os.path.basename(obj) not in ("Verilator.o", "VlcMain.o")
    and not obj.endswith("__header_cc.o")
]
source = os.path.relpath(os.path.abspath("t/t_a3_selftest_thread.cpp"),
                         os.path.abspath(test.root + "/src/obj_dbg"))
executable = os.path.abspath(test.obj_dir + "/static_assertion")
obj = executable + ".o"
macros = executable + ".macros"
rules = executable + ".mk"
test.write_wholefile(
    rules,
    "static_thread_fixture:\n\t$(CXX) $(CXXFLAGS) $(CPPFLAGSWALL) -c " + source
    + " -o " + obj + " && $(LINK) $(LDFLAGS) -o " + executable + " " + obj + " "
    + ' '.join(objects) + " $(CCMALLOC) $(LIBS)\n"
    + "static_thread_macros:\n\t$(CXX) $(CXXFLAGS) $(CPPFLAGSWALL) -dM -E " + source
    + " -MF " + obj + ".macros.d > " + macros + "\n")
test.run(cmd=[os.environ['MAKE'], "-C", test.root + "/src/obj_dbg", "-f", "../Makefile_obj",
              "-f", rules, "VL_DEBUG=1", "static_thread_fixture", "static_thread_macros"])
test.run(cmd=[executable], logfile=test.obj_dir + "/static_valid.log")
modes = ["direct"]
profile = test.file_contents(macros)
if re.search(r'^#define VL_USER_TYPE_CHECKS\b', profile, re.MULTILINE):
    modes += ["pointer", "integer"]
for mode in modes:
    test.run(cmd=[executable, mode], fails='any',
             logfile=test.obj_dir + "/static_" + mode + ".log",
             expect_filename="t/t_a3_selftest_thread_" + mode + ".out")

test.passes()
