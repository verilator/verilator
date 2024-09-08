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
    os.environ["VERILATOR_ROOT"] + "/bin/verilator_coverage",
    "--no-unlink",
    "--nounlink",
    "--write",
    test.obj_dir + "/coverage.dat",
    "t/t_vlcov_data_a.dat",
    "t/t_vlcov_data_b.dat",
    "t/t_vlcov_data_c.dat",
    "t/t_vlcov_data_d.dat",
],
         verilator_run=True)

# Not deleted e.g. parsed --no-unlink properlytest.files_identical(test.t_dir + "/t_vlcov_data_a.dat", test.t_dir + "/t_vlcov_data_a.dat")

# Older clib's didn't properly sort maps, but the coverage data doesn't
# really care about ordering. So avoid false failures by sorting.test.files_identical_sorted(test.obj_dir + "/coverage.dat", test.golden_filename)

test.passes()
