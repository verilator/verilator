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

# If a test fails, broken .cmake may disturb the next run
test.clean_objs()

test.priority(30)
test.scenarios('vlt')
test.top_filename = "t/t_hier_block.v"

threads = '-DTEST_THREADS=1'

if not test.have_cmake:
    test.skip("Test requires CMake; ignore error since not available or version too old")

# Build through a symlink, so the logical and physical build paths differ
os.mkdir(test.obj_dir + "/real")
os.symlink("real", test.obj_dir + "/link")
build_dir = test.obj_dir + "/link"
source_dir = test.t_dir + "/t_hier_block_cmake"
# CMake DIRECTORY is relative to the source directory
directory = os.path.relpath(os.path.abspath(build_dir + "/vdir"), source_dir)

test.run(logfile=test.obj_dir + "/cmake.log",
         cmd=[
             'cd "' + build_dir + '" && cmake ' + source_dir,
             "-DCMAKE_PREFIX_PATH=" + os.environ["VERILATOR_ROOT"], threads,
             "-DTEST_DIRECTORY=" + directory
         ])

test.run(logfile=test.obj_dir + "/build.log",
         cmd=[
             'cd "' + build_dir + '" && cmake --build', '.', ('-v' if test.verbose else ''),
             '-j ' + str(test.max_procs), '--', "CXX_FLAGS=" + threads
         ])

test.run(logfile=test.obj_dir + "/run.log",
         cmd=['cd "' + build_dir + '" && ./t_hier_block_cmake', '.'])

test.passes()
