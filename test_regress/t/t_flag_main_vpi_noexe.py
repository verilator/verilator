#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2025 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt')

# --vpi without --exe (no generated main, library-only output): the Makefile
# must still report VM_VPI = 1, but must NOT add the runtime-VPI link flags since
# there is no executable to export VPI symbols from.  Exercises the exe()==false
# branch of the VPI link-flag gate in V3EmitMk.
test.top_filename = 't/t_flag_main_vpi.v'

test.compile(make_main=False, verilator_make_gmake=False, verilator_flags2=["--vpi --timing"])

test.file_grep(test.obj_dir + "/V" + test.name + "_classes.mk", r'VM_VPI = 1')
# Without --exe there is no executable to export symbols from or to dlopen into,
# so the runtime-VPI link flags (CFG_LDFLAGS_DYNAMIC/CFG_LDLIBS_DYNAMIC, probed at
# configure time) must not be referenced in the generated Makefile.
mk = test.obj_dir + "/V" + test.name + ".mk"
test.file_grep_not(mk, r'CFG_LDFLAGS_DYNAMIC')
test.file_grep_not(mk, r'CFG_LDLIBS_DYNAMIC')

test.passes()
