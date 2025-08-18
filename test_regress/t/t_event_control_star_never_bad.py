#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2025 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('linter')
test.top_filename = 't/t_event_control_star_never.v'

root = ".."

if not os.path.exists(root + "/.git"):
    test.skip("Not in a git repository")

test.lint(verilator_flags2=['--timing'], fails=True, expect_filename=test.golden_filename)

test.extract(in_filename=test.top_filename,
             out_filename=root + "/docs/gen/ex_ALWNEVER_faulty.rst",
             lines="9-9")

test.extract(in_filename=test.golden_filename,
             out_filename=root + "/docs/gen/ex_ALWNEVER_msg.rst",
             lines="1-1")

test.passes()
