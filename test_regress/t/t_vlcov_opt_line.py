#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('dist')

test.run(cmd=[
    os.environ["VERILATOR_ROOT"] + "/bin/verilator_coverage", "--write-info",
    test.obj_dir + "/coverage.info", "--filter-type line", "t/t_vlcov_data_e.dat"
],
         verilator_run=True)

test.files_identical(test.obj_dir + "/coverage.info", "t/" + test.name + ".info.out")

test.passes()
