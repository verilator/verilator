#!/usr/bin/env python3
# DESCRIPTION: Verilator: FSM case(state_d) overwritten-default warning test
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt')

# A canonical `state_d = state_q` default followed by another top-level write
# to `state_d` before `case (state_d)` is legal RTL, but it is not the narrow
# Phase 1 shape we support. Warn and reject rather than silently skipping it.
test.compile(verilator_flags2=["--cc --coverage"], fails=True)

test.file_grep(
    test.compile_log_filename,
    r'%Warning-COVERIGN: t/t_cover_fsm_nextstate_overwrite_warn.v:\d+:\d+: Ignoring '
    r'unsupported: FSM coverage on case\(state_d\) when the canonical state_d = state_q '
    r'default is overwritten before the case statement')

test.passes()
