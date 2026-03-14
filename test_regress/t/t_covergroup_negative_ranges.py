#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt')

test.compile(verilator_flags2=['--coverage'])

test.execute()

test.covergroup_coverage_report()
test.files_identical(test.obj_dir + '/covergroup_report.txt', test.golden_filename)

test.passes()
