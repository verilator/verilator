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

test.compile()

test.execute(all_run_flags=["+verilator+debug +verilator+debugi+9 +verilator+rand+reset+1"],
             expect=r'.*Verilated::debug is on.*')

test.execute(all_run_flags=["+verilator+help"],
             fails=True,
             expect=r".*For help, please see 'verilator --help'.*")

test.execute(all_run_flags=["+verilator+V"], fails=True, expect=r'.*Version:.*')

test.execute(all_run_flags=["+verilator+version"], fails=True, expect=r'.*Version:.*')

test.passes()
