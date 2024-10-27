#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap
import shutil

test.scenarios('dist')

tmp = test.obj_dir + "/copied.dat"
shutil.copy(test.t_dir + "/t_vlcov_data_a.dat", tmp)

test.run(cmd=[
    os.environ["VERILATOR_ROOT"] + "/bin/verilator_coverage", "--unlink", tmp, "--write",
    test.obj_dir + "/output.dat"
],
         verilator_run=True)

test.files_identical(test.obj_dir + "/output.dat", "t/t_vlcov_data_a.dat")

# --unlink should have removed it
if os.path.exists(tmp):
    test.error("Wan't unlinked")

test.passes()
