#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt')

if not test.have_gpu:
    test.skip("No CUDA GPU available")

test.compile(
    verilator_flags2=["--binary", "--gpu", "--gpu-dpi", "job_seed", test.t_dir + "/t_gpu_jobs.cu"])

jobs = test.obj_dir + "/jobs.txt"
test.write_wholefile(
    jobs, "first +seed=3\n"
    "second +seed=7 +limit=45\n"
    "stopped +seed=5\n"
    "third +seed=11\n")

test.execute(run_env="VERILATOR_GPU_JOBS=" + jobs + " VERILATOR_GPU_LOGDIR=" + test.obj_dir +
             " VERILATOR_GPU_SLOTS=2",
             check_finished=False)

summary = test.obj_dir + "/gpu_batch_summary.txt"
test.file_grep(summary, r'^first PASS 205$')
test.file_grep(summary, r'^second FAIL ')
test.file_grep(summary, r'^stopped FAIL 205$')
test.file_grep(summary, r'^third PASS 205$')

test.file_grep(test.obj_dir + "/first.log", r'seed=3 cyc=20 lfsr=1572864 time=205')
test.file_grep(test.obj_dir + "/third.log", r'seed=11 cyc=20 lfsr=5767168 time=205')
test.file_grep(test.obj_dir + "/second.log", r'job argument \+limit=45 is read by the design')
test.file_grep(test.obj_dir + "/stopped.log", r'Verilog \$stop')

test.execute(run_env="VERILATOR_GPU_RESIDENT=0", all_run_flags=["+seed=3"])
test.file_grep(test.run_log_filename, r'seed=3 cyc=20 lfsr=1572864 time=205')

test.passes()
