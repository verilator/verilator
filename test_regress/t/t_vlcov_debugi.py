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

for basename in [
        "t_vlcov_data_a.dat", "t_vlcov_data_b.dat", "t_vlcov_data_c.dat", "t_vlcov_data_d.dat"
]:
    test.run(cmd=[
        os.environ["VERILATOR_ROOT"] + "/bin/verilator_coverage", "t/" + basename, "--debug",
        "--debugi 9"
    ],
             tee=test.verbose,
             verilator_run=True)

test.passes()
