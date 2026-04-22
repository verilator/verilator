#!/usr/bin/env python3
# DESCRIPTION: Verilator: FSM enum width limit test
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt')

# FSM coverage currently stores recovered enum state values in the detector's
# 32-bit internal representation, so wider enum-backed FSMs are rejected.
test.lint(
    verilator_flags2=["--coverage-fsm"],
    fails=True)

test.file_grep(
    test.compile_log_filename,
    r'%Warning-COVERIGN: t/t_cover_fsm_enumwide_bad.v:25:7: Ignoring unsupported: '
    r'FSM coverage on enum-typed state variables wider than 32 bits')

test.passes()
