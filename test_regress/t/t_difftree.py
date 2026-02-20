#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2024 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('dist')

if not os.path.exists(os.environ["VERILATOR_ROOT"] + "/bin/verilator_difftree"):
    test.skip("No verilator_difftree available")

test.run(cmd=[
    "cd " + test.obj_dir + " && " + os.environ["VERILATOR_ROOT"] + "/bin/verilator_difftree",
    test.t_dir + "/t_difftree.a.tree", test.t_dir + "/t_difftree.b.tree > diff.log"
],
         fails=1)  # Testing mismatch, so exit code 1

test.files_identical(test.obj_dir + "/diff.log", test.golden_filename, 'logfile')

test.passes()
