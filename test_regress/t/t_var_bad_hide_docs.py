#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('linter')

root = ".."

if not os.path.exists(root + "/.git"):
    test.skip("Not in a git repository")

test.lint(verilator_flags2=["--lint-only -Wwarn-VARHIDDEN"],
          fails=test.vlt_all,
          expect_filename=test.golden_filename)

test.extract(in_filename=test.top_filename,
             out_filename=root + "/docs/gen/ex_VARHIDDEN_faulty.rst",
             regexp=r'(module t|integer|endmodule)')

test.extract(in_filename=test.golden_filename,
             out_filename=root + "/docs/gen/ex_VARHIDDEN_msg.rst",
             lineno_adjust=-6,
             regexp=r'(var_bad_hide)')

test.passes()
