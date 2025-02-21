#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2025 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt')

stdout_filename = os.path.join(test.obj_dir, test.name + ".out")

test.compile(
    # Override default flags
    v_flags=[''],
    verilator_flags=[
        "-E -P --preproc-resolve t/t_preproc_resolve_config.vlt -y t/t_preproc_resolve"
    ],
    verilator_flags2=[''],
    verilator_flags3=[''],
    verilator_make_gmake=False,
    make_top_shell=False,
    make_main=False,
    stdout_filename=stdout_filename)

test.files_identical(stdout_filename, test.golden_filename)

test.passes()
