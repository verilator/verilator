#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2025 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt')

test.lint(verilator_flags2=['-Wall -Wno-DECLFILENAME'],
          fails=True,
          expect_filename=test.golden_filename)

test.extract(in_filename=test.top_filename,
             out_filename="../docs/gen/ex_PROCASSINIT_faulty.rst",
             lines="26-32")

test.extract(in_filename=test.top_filename,
             out_filename="../docs/gen/ex_PROCASSINIT_fixed.rst",
             lines="36-45")

test.extract(in_filename=test.golden_filename,
             out_filename="../docs/gen/ex_PROCASSINIT_msg.rst",
             lines="1-9")

test.passes()
