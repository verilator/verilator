#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('simulator')
test.top_filename = "t/t_flag_make_cmake.v"

# We expect below that Vt_flag_verilate.mk and others are not in the build
# tree already when doing --no-verilate, so we must remove them when
# re-running the test.
test.clean_objs()

test.compile(  # Don't call cmake nor gmake from driver.py. Nothing should be done here.
    verilator_make_cmake=False,
    verilator_make_gmake=False,
    verilator_flags2=['--exe --cc --no-verilate', '../' + test.main_filename])

# --no-verilate should skip Verilation
if os.path.exists(test.obj_dir + '/Vt_flag_verilate.mk'):
    test.error('Vt_flag_verilate.mk is unexpectedly created')

# --verilate this time
test.compile(  # Don't call cmake nor gmake from driver.py. Just verilate here.
    verilator_make_cmake=False,
    verilator_make_gmake=False,
    verilator_flags2=['--exe --cc --verilate', '../' + test.main_filename])

# must be verilated this time
if not os.path.exists(test.obj_dir + '/Vt_flag_verilate.mk'):
    test.error('Vt_flag_verilate.mk does not exist')

# Just build, no Verilation. .tree must not be saved even with --dump-tree option.
test.compile(  # Don't call cmake nor gmake from driver.py. Just build here
    verilator_flags2=[
        '--exe --cc --build --no-verilate', '../' + test.main_filename,
        '--debugi 1 --dump-tree --dump-tree-addrids'
    ])

# The previous run must not verilated, only build is expected.
if os.path.exists(test.obj_dir + '/Vt_flag_verilate_990_final.tree'):
    test.error('Unexpectedly verilated.')

test.execute()

test.passes()
