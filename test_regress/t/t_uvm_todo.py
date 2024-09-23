#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap
import multiprocessing

test.scenarios('vlt')

test.compile(
    v_flags2=[
        "--timing",  #
        "-Wno-PKGNODECL -Wno-IMPLICITSTATIC -Wno-MISINDENT",
        "-Wno-CASEINCOMPLETE -Wno-CASTCONST -Wno-SYMRSVDWORD -Wno-WIDTHEXPAND -Wno-WIDTHTRUNC",
        "-Wno-REALCVT"  # TODO note mostly related to $realtime - could suppress or fix upstream
    ],
    make_flags=['-k -j ' + str(multiprocessing.cpu_count())],
    verilator_make_gmake=False)

#test.execute()

test.passes()
