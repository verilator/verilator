#!/usr/bin/env python3
# DESCRIPTION: Verilator: FSM register wrapper VLT warning coverage
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt')

test.lint(
    verilator_flags2=["--coverage-fsm", "-fno-inline", "t/t_fsm_register_wrapper_warn_bad.vlt"],
    fails=True,
    expect_filename=test.golden_filename,
)

test.passes()
