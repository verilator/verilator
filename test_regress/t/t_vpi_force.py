#!/usr/bin/env python3
# DESCRIPTION: vpi force and release test
# This test checks that forcing a signal using vpi_put_value with vpiForceFlag
# sets it to the correct value, and then releasing it with vpiReleaseFlag
# returns it to the initial state. This is a basic test that just checks the
# correct behavior for a clocked register being forced with a VpiIntVal.
#
# Copyright 2025 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('simulator')

test.compile(make_top_shell=False,
             make_main=False,
             make_pli=True,
             verilator_flags2=["--main --exe --vpi --timing", test.pli_filename])

test.execute(use_libvpi=True, check_finished=True)

test.passes()
