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

test.unlink_ok(test.obj_dir + "/t_sys_file_scan_test.log")

test.compile()

test.execute()

test.file_grep(test.obj_dir + "/t_sys_file_scan_test.log", r"""# a
          1
""")

test.passes()
