#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt')

test.lint(fails=True, verilator_flags2=['-Wno-fatal --diagnostics-sarif --no-skip-identical'])

sarif_filename = test.obj_dir + "/" + test.vm_prefix + ".sarif"

# Make sure V3Error meta comments aren't in any outputs
test.file_grep_not(sarif_filename, r'__WARN')

# Fixes: spelling suggestion (the lint_off/lint_on fixes are covered by t_sarif)
test.file_grep(sarif_filename, r'"fixes"')
test.file_grep(sarif_filename, r'"text": "Replace \'foobat\' with \'foobar\'"')
test.file_grep_not(sarif_filename, r'lint_off')

test.files_identical(sarif_filename, "t/" + test.name + ".sarif.out", "logfile")

test.passes()
