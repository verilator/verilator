#!/usr/bin/env python3
# DESCRIPTION: Test failure of trying to force a non-forceable signal
# This test checks that attempting to force a signal that is not marked as
# forceable causes an error under Verilator, and does not cause an error in
# other simulators that do not need this metacomment to be able to force
# signals.
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
             verilator_flags2=["--main --exe --vpi", test.pli_filename])

test.execute(use_libvpi=True,
             fails=test.vlt_all,
             expect_filename=test.golden_filename,
             check_finished=test.iv)  # or check_finished=test.xrun

test.passes()
