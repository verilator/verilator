#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap
import runpy

test.scenarios('vlt')
test.top_filename = test.obj_dir + "/" + test.name + ".v"
test.golden_filename = test.obj_dir + "/" + test.name + ".out"

# Rather then having to maintain a new .v and .out, add returns
# to all lines of the existing t_preproc test.

wholefile = test.file_contents(test.t_dir + "/t_preproc.v")
wholefile = re.sub(r'\n', r'\r\n', wholefile)
test.write_wholefile(test.obj_dir + "/" + test.name + ".v", wholefile)

wholefile = test.file_contents(test.t_dir + "/t_preproc.out")
wholefile = re.sub(r't/t_preproc.v', test.obj_dir + "/t_preproc_dos.v", wholefile)  # Fix `line's
test.write_wholefile(test.golden_filename, wholefile)

runpy.run_path('t/t_preproc.py', globals())
