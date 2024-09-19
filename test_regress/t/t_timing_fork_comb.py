#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('simulator')

# Should convert the first always into combo and detect cycle
test.compile(fails=True, verilator_flags2=["--timing"])

test.file_grep(
    test.compile_log_filename,
    r'%Warning-UNOPTFLAT: t/t_timing_fork_comb.v:\d+:\d+: Signal unoptimizable: Circular combinational logic:'
)

test.compile(verilator_flags2=["--exe --main --timing -Wno-UNOPTFLAT"])

test.execute()

test.passes()
