#!/usr/bin/env python3
# DESCRIPTION: Scope hierarchy map clearing upon VerilatedModel destruction
# VerilatedImp::s() is a VerilatedImpData singleton that contains an m_hierMap
# whose keys are pointers to VerilatedScope objects. Because it is a
# singleton, it is not automatically destroyed together with the
# VerilatedModel, so this test checks that the VerilatedSyms destructor that is
# invoked upon the VerilatedModel's destruction clears the keys from the map.
#
# Copyright 2025 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt_all')

test.compile(make_top_shell=False,
             make_main=False,
             verilator_flags2=["--exe --vpi", test.pli_filename])

test.execute()

test.passes()
