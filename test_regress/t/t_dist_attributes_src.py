#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2024 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.priority(30)
test.scenarios('dist')
test.rerunnable = False


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
if not os.path.exists(test.root + "/src/obj_dbg/compile_commands.json"):
    test.skip("compile_commands.json not found. Please install 'bear > 3.0' and rebuild Verilator")
if not have_clang_check():
    test.skip("No libclang installed")

# some of the files are only used in Verilation
# and are only in "include" folder
srcfiles = test.glob_some(test.root +
                          "/src/*.cpp") + test.glob_some(test.root +
                                                         "/src/obj_dbg/V3Const__gen.cpp")
srcfiles = [f for f in srcfiles if re.search(r'\/(V3Const|Vlc\w*|\w*_test|\w*_sc|\w*.yy).cpp$', f)]
srcfiles_str = " ".join(srcfiles)

test.run(logfile=test.run_log_filename,
         tee=True,
         cmd=["python3", test.root + "/nodist/clang_check_attributes",
              "--verilator-root=" + test.root,
              "--compilation-root=" + test.root + "/src/obj_dbg",
              "--compile-commands-dir=" + test.root + "/src/obj_dbg",
              srcfiles_str])  # yapf:disable

test.file_grep(test.run_log_filename, r'Number of functions reported unsafe: +(\d+)', 0)

# Source-only checked conversions must terminate without compiler global teardown.
executable = test.obj_dir + "/user_slots"
flags = "--coverage -DVL_GCOV" if test.have_dev_gcov else ""
if test.have_dev_asan:
    flags += " -fsanitize=address"
test.run(cmd=[
    os.environ['CXX'], "-std=c++17", "-pthread", flags, "-I" + test.root + "/include", "-I" +
    test.root + "/src", "-I" + test.root + "/src/obj_dbg", "-I" + test.root +
    "/src/obj_opt", "t/t_dist_attributes_src.cpp", "-o", executable
])
test.run(cmd=[executable], logfile=test.obj_dir + "/slots_valid.log")
for mode, golden in [("integer", "t/t_dist_attributes_src_integer.out"),
                     ("pointer", "t/t_dist_attributes_src_pointer.out"),
                     ("worker", "t/t_dist_attributes_src_integer.out")]:
    test.run(cmd=[executable, mode],
             fails='any',
             logfile=test.obj_dir + "/slots_" + mode + ".log",
             expect_filename=golden)

test.passes()
