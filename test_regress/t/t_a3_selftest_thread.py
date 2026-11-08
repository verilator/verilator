#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2024 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import os

import vltest_bootstrap

test.priority(100)
test.scenarios('vltmt')
test.top_filename = "t/t_EXAMPLE.v"

test.lint(threads=2, v_flags=["--verilate-jobs 2 --debug-self-test"])

# Link the existing compiler objects, replacing only its command-line entry point.
objects = [obj for obj in test.glob_some(test.root + "/src/obj_dbg/*.o")
           if os.path.basename(obj) not in ("Verilator.o", "VlcMain.o")
           and not obj.endswith("__header_cc.o")]
executable = test.obj_dir + "/static_assertion"
flags = ["-DVL_USER_TYPE_CHECKS"]
if test.have_dev_asan:
    flags += ["-fsanitize=address"]
if test.have_dev_gcov:
    flags += ["--coverage", "-DVL_GCOV"]
query = (os.environ['MAKE'] + " -s -C " + test.root + "/src/obj_dbg -f ../Makefile_obj ")
compiler = test.run_capture(
    query + "--eval 'print_static_cxx:;@echo $(CXX)' print_static_cxx").strip()
libraries = test.run_capture(
    query + "--eval 'print_static_libs:;@echo $(LIBS)' print_static_libs").split()
test.run(cmd=[compiler, "-std=c++17", "-pthread", "-DVL_DEBUG", "-D_GLIBCXX_DEBUG",
              *flags, "-I" + test.root + "/include", "-I" + test.root + "/src",
              "-I" + test.root + "/src/obj_dbg", "t/t_a3_selftest_thread.cpp",
              *objects, *libraries, "-o", executable])
test.run(cmd=[executable], logfile=test.obj_dir + "/static_valid.log")
for mode in ["pointer", "integer"]:
    test.run(cmd=[executable, mode], fails='any',
             logfile=test.obj_dir + "/static_" + mode + ".log",
             expect_filename="t/t_a3_selftest_thread_" + mode + ".out")

test.passes()
