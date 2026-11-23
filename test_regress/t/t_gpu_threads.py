#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vltmt')

test.top_filename = "t/t_gpu_basic.v"

if not test.have_gpu:
    test.skip("No CUDA GPU available")

test.compile(threads=2, verilator_flags2=["--binary", "--gpu"])

test.execute()

test.execute(run_env="VERILATOR_GPU_BATCH=3")

test.passes()
