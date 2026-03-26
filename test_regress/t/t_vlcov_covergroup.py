#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-FileCopyrightText: 2024 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('dist')

test.run(cmd=[
    os.environ["VERILATOR_ROOT"] + "/bin/verilator_coverage",
    "--covergroup",
    test.t_dir + "/t_vlcov_covergroup_data.dat",
],
         logfile=test.obj_dir + "/covergroup.log",
         tee=False,
         verilator_run=True)

test.files_identical(test.obj_dir + "/covergroup.log", test.golden_filename)

test.passes()
