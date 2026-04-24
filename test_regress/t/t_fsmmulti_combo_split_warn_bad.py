#!/usr/bin/env python3
# DESCRIPTION: Verilator: FSMMULTI warning test for duplicate split FSM transition blocks
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt')

test.lint(verilator_flags2=["--coverage-fsm"], fails=True)

test.file_grep(
    test.compile_log_filename,
    r'%Warning-FSMMULTI: t/t_fsmmulti_combo_split_warn_bad.v:29:5: FSM coverage: multiple '
    r'supported transition candidates found for the same FSM in combinational always blocks. '
    r'Only the first candidate will be instrumented.')

test.passes()
