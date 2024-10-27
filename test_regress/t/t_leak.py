#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt_all')

if test.vltmt and test.getenv_def('TRAVIS_DIST', "None") == "trusty":
    test.skip("Multithreaded test does not work under CI w/ Ubuntu Trusty")

test.compile(make_top_shell=False,
             make_main=False,
             verilator_flags2=["--exe", test.pli_filename],
             make_flags=['CPPFLAGS_ADD=-DVL_NO_LEGACY'])

test.execute()

test.passes()
