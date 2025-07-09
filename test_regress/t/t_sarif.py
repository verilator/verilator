#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt')

test.lint(verilator_flags2=['-Wno-fatal --diagnostics-sarif'],
          expect_filename=test.golden_filename)

sarif_filename = test.obj_dir + "/" + test.vm_prefix + ".sarif"

# Make sure V3Error meta comments aren't in any outputs
test.file_grep_not(test.compile_log_filename, r'__WARN')
test.file_grep_not(sarif_filename, r'__WARN')

test.files_identical(sarif_filename, "t/" + test.name + ".sarif.out", "logfile")

# Check that sarif parses
nout = test.run_capture("sarif --version", check=False)
version_match = re.search(r'SARIF tools', nout, re.IGNORECASE)
if not version_match:
    test.skip("sarif is not installed")

html_filename = test.obj_dir + "/validation.html"

test.run(cmd=['sarif', 'html', sarif_filename, '--output', html_filename])

# Validator:
#   https://sarifweb.azurewebsites.net/Validation

# Rewrite
# test.run(cmd=['sarif copy t/t_sarif.out --output ' + test.obj_dir + '/t_sarif.out.rewrite'])

test.passes()
