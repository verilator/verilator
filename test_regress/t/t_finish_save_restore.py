#!/usr/bin/env python3
# DESCRIPTION: Verilator: Save and restore $finish propagation state
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt', 'vltmt')

test.compile(
    make_main=False,
    verilator_flags2=['--savable', '--exe', test.pli_filename, '-CFLAGS', '-DVL_USER_FINISH'])
test.execute(all_run_flags=[f'+SAVE_FILE={test.obj_dir}/saved.vltsv'])

test.passes()
