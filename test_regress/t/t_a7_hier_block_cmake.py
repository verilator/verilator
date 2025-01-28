#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap
import multiprocessing

# If a test fails, broken .cmake may disturb the next run
test.clean_objs()

test.scenarios('simulator')
test.top_filename = "t/t_hier_block.v"

threads = ('-DTEST_THREADS=6' if test.vltmt else '-DTEST_THREADS=1')

if not test.have_cmake:
    test.skip("Test requires CMake; ignore error since not available or version too old")

test.run(logfile=test.obj_dir + "/cmake.log",
         cmd=[
             'cd "' + test.obj_dir + '" && cmake ' + test.t_dir + '/t_hier_block_cmake',
             "-DCMAKE_PREFIX_PATH=" + os.environ["VERILATOR_ROOT"], threads
         ])

test.run(logfile=test.obj_dir + "/build.log",
         cmd=[
             'cd "' + test.obj_dir + '" && cmake --build', '.', ('-v' if test.verbose else ''),
             '-j ' + str(multiprocessing.cpu_count()), '--', "CXX_FLAGS=" + str(threads)
         ])

test.run(logfile=test.obj_dir + "/run.log",
         cmd=['cd "' + test.obj_dir + '" && ./t_hier_block_cmake', '.'])

target_dir = test.obj_dir + '/CMakeFiles/t_hier_block_cmake.dir/Vt_hier_block.dir/'
test.file_grep(target_dir + 'Vsub0/sub0.sv', r'^module\s+(\S+)\s+', "sub0")
test.file_grep(target_dir + 'Vsub1/sub1.sv', r'^module\s+(\S+)\s+', "sub1")
test.file_grep(target_dir + 'Vsub2/sub2.sv', r'^module\s+(\S+)\s+', "sub2")
test.file_grep(target_dir + 'Vt_hier_block__stats.txt',
               r'HierBlock,\s+Hierarchical blocks\s+(\d+)', 14)
test.file_grep(test.obj_dir + '/run.log', r'MACRO:(\S+) is defined', "cplusplus")

test.passes()
