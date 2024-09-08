#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test module for prepareClone/atClone APIs
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt_all')

test.compile(make_top_shell=False,
             make_main=False,
             verilator_flags2=["--exe", test.pli_filename, "-cc"],
             threads=(2 if test.vltmt else 1))

test.execute(expect_filename=test.golden_filename)

test.passes()
