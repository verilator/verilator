#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('simulator4')
test.top_filename = "t/t_fourstate_cond.v"

test.compile(verilator_flags2=['--binary', '--coverage-line', '--coverage-expr'])

test.execute(all_run_flags=["+verilator+coverage+file+" + test.coverage_filename])

test.run(cmd=[
    os.environ["VERILATOR_ROOT"] + "/bin/verilator_coverage",
    "--annotate",
    test.obj_dir + "/annotated",
    test.coverage_filename,
],
         verilator_run=True)

test.files_identical(test.obj_dir + "/annotated/t_fourstate_cond.v", test.golden_filename)

test.passes()
