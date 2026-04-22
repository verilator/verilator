#!/usr/bin/env python3
# DESCRIPTION: Verilator: FSM enum transition bad-value test
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt')

# When an enum-backed FSM assigns a constant that is not one of the declared
# enum items, FSM coverage should warn and skip the unsupported edge rather
# than turning optional coverage into a hard compile failure.
test.lint(
    verilator_flags2=["--coverage-fsm"],
    fails=True)

test.file_grep(
    test.compile_log_filename,
    r'%Warning-COVERIGN: t/t_cover_fsm_enum_bad.v:27:19: Ignoring unsupported: FSM coverage '
    r'on enum state transitions that assign a constant not present in the declared enum')

test.passes()
