#!/usr/bin/env python3
# DESCRIPTION: Verilator: FSM coverage multi-reset assignment warning test
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt')

# Multiple reset assignments to the same FSM state variable are legal RTL but
# not a realistic reset style to model as distinct reset arcs. Warn and ignore
# reset-arc extraction for that branch instead of inventing multiple ANY->state
# coverage edges.
test.lint(verilator_flags2=["--coverage-fsm"], fails=True)

test.file_grep(
    test.compile_log_filename,
    r'%Warning-COVERIGN: t/t_cover_fsm_reset_multi.v:\d+:\d+: Ignoring unsupported: FSM '
    r'coverage on reset branches with multiple assignments to the state variable')

test.passes()
