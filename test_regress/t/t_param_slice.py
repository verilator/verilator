#!/usr/bin/env python3
# DESCRIPTION: Verilator: Test constant parameter slicing of unpacked arrays (issue #6257)
#
# Copyright 2025 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
import vltest_bootstrap

test.scenarios('vlt')

test.compile(verilator_flags2=['--exe', '--main', '--timing'])

test.execute()

test.passes()
