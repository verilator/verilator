#!/usr/bin/env python3
# DESCRIPTION: Verilator: Reject skipped NBA lowering without AST export
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Verilator Authors
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt')
test.top_filename = "t/t_ast_pre_codegen.v"

test.lint(verilator_flags2=['-fno-delayed'], fails=True, expect_filename=test.golden_filename)

test.passes()
