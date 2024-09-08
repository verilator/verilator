#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

# show-config: This test runs the very first time we've executed Verilator
# after building so we make sure to run with --gdbbt, so if it dumps we'll
# get a trace.

import vltest_bootstrap

test.scenarios('vlt')

DEBUG_QUIET = "--debug --debugi 0 --gdbbt --no-dump-tree"

test.run(
    cmd=[
        "perl",
        os.environ["VERILATOR_ROOT"] + "/bin/verilator",  #
        DEBUG_QUIET,
        "-V"
    ],
    verilator_run=True)

test.compile(verilator_flags2=[DEBUG_QUIET, "--trace"])

test.execute()

test.passes()
