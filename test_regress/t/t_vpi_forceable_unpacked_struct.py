#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test module
#
# This file ONLY is placed under the Creative Commons Public Domain.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: CC0-1.0

import vltest_bootstrap

test.scenarios('vlt')

test.compile(make_top_shell=False,
             make_main=False,
             verilator_flags2=["--vpi", "--exe", "--public-flat-rw", test.pli_filename])

test.execute()

test.passes()
