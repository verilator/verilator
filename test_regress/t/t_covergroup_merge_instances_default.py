#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

from coverage_common import init_log, run_vlcov, vlcov_run_context

test.scenarios('vlt')

test.compile(verilator_flags2=['--coverage-user', '--coverage-merge-instances'])

test.execute()

# The coverage the report computes: as get_coverage() does, except for cg_multi_off, whose
# instances the coverage database merges
log = test.obj_dir + "/vlcov.log"
tmp_log = test.obj_dir + "/vlcov.tmp"
init_log(log)
vlcov = vlcov_run_context(test, log, tmp_log)
run_vlcov(vlcov,
          "verilator_coverage --report hierarchy --levels 1 coverage.dat",
          args=["--report", "hierarchy", "--levels", "1", test.obj_dir + "/coverage.dat"])

test.files_identical(log, test.golden_filename)

test.passes()
