#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('dist')
test.rerunnable = False

root = ".."


def have_clang_check():
    cmd = 'python3 -c "from clang.cindex import Index; index = Index.create(); print(\\"Clang imported\\")";'
    if test.verbose:
        print("\t" + cmd)
    nout = test.run_capture(cmd, check=False)
    if not nout or not re.search(r'Clang imported', nout):
        return False
    return True


if 'VERILATOR_TEST_NO_ATTRIBUTES' in os.environ:
    test.skip("Skipping due to VERILATOR_TEST_NO_ATTRIBUTES")
if not os.path.exists(root + "/src/obj_dbg/compile_commands.json"):
    test.skip("compile_commands.json not found. Please install 'bear > 3.0' and rebuild Verilator")
if not have_clang_check():
    test.skip("No libclang installed")

# some of the files are only used in Verilation
# and are only in "include" folder
srcfiles = test.glob_some(root + "/include/*.cpp")
srcfiles_str = " ".join(srcfiles)
clang_args = "-I" + root + "/include/ -I" + root + "/include/vltstd/ -fcoroutines-ts"

test.run(logfile=test.run_log_filename,
         tee=True,
         cmd=["python3", root + "/nodist/clang_check_attributes",
              "--verilator-root=" + root,
              "--cxxflags='" + clang_args + "'",
              srcfiles_str])  # yapf:disable

test.file_grep(test.run_log_filename, r'Number of functions reported unsafe: +(\d+)', 0)

test.passes()
