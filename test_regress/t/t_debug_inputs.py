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

test.lint(v_flags=["--debug --debugi 1 -Wno-MULTITOP t/t_debug_inputs_b.v"])

test.file_grep(test.obj_dir + "/V" + test.name + "__inputs.vpp", r'module t_debug_inputs ')
test.file_grep(test.obj_dir + "/V" + test.name + "__inputs.vpp", r'module t_debug_inputs_a ')
test.file_grep(test.obj_dir + "/V" + test.name + "__inputs.vpp", r'module t_debug_inputs_b ')

test.passes()
