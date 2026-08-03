#!/usr/bin/env python3
# DESCRIPTION: Verilator: Gate deduplication with function captures
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Jose Tejada
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('simulator')

test.compile(verilator_flags2=[
    '--top-module', 'game_test', '-Wno-fatal', '-Wno-IMPLICIT',
    '-Wno-WIDTHEXPAND', '-Wno-WIDTHTRUNC',
])

test.passes()
