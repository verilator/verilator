#!/usr/bin/env python3
# DESCRIPTION: Verilator: FSM coverage warns on plain always with edge sensitivity
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt')

test.compile(verilator_flags2=['--cc --coverage-fsm'], fails=True)

test.file_grep(
    test.compile_log_filename,
    r'%Warning-COVERIGN: t/t_cover_fsm_plain_always_edge_bad.v:\d+:\d+: Ignoring unsupported: '
    r'FSM coverage on plain always blocks requires a combinational sensitivity list or '
    r'always_comb')

test.passes()
