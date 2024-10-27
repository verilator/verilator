#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt')

out_filename = test.obj_dir + "/V" + test.name + ".tree.json"

test.compile(verilator_flags2=['--no-std', '--json-only', '--no-json-edit-nums', '--flatten'],
             verilator_make_gmake=False,
             make_top_shell=False,
             make_main=False)

test.files_identical(out_filename, test.golden_filename)

test.passes()
