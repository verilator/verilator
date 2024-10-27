#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

# 8-Mar-2012: Modifications for this test contributed by Jeremy Bennett and
# Jie Xu.

import vltest_bootstrap

test.scenarios('simulator')

test.compile(make_top_shell=False,
             make_main=False,
             verilator_flags2=["-Wno-BLKANDNBLK -language 1800-2005 --exe", test.pli_filename])

test.execute()

test.passes()
