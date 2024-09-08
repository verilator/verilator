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
test.top_filename = "t/t_assert_elab.v"

test.unlink_ok(test.obj_dir + "/t_assert_elab_bad.log")

test.compile(v_flags2=[
    '+define+FAILING_ASSERTIONS', ('--assert' if test.vlt_all else ('+assert' if test.nc else ''))
],
             fails=True)

test.execute(fails=test.vlt_all)

test.file_grep(test.obj_dir + "/vlt_compile.log",
               r'%Warning-USERFATAL: "Parameter   5 is invalid...string and constant both work"')

test.passes()
