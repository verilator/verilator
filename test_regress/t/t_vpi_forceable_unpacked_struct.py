#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test module
#
# This file ONLY is placed under the Creative Commons Public Domain.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: CC0-1.0

import vltest_bootstrap

test.scenarios("vlt_all", "xrun")

test.compile(
    make_top_shell=False,
    make_pli=True,
    verilator_flags2=["--binary", "--vpi", "--no-l2name", "--public-flat-rw", test.pli_filename])

test.execute(use_libvpi=True)

test.passes()
