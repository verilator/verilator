#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt')

test.compile(make_top_shell=False,
             make_main=1,
             verilator_make_gmake=True,
             verilator_flags2=["--exe --pins-inout-enables --no-timing -Wno-STMTDLY"])

test.file_grep_not(test.obj_dir + "/" + test.vm_prefix + ".h", r'internal_sub_io__out')
test.file_grep_not(test.obj_dir + "/" + test.vm_prefix + ".h", r'internal_sub_io__en')

test.passes()
