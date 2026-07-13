#!/usr/bin/env python3
# DESCRIPTION: Verilator: MT message wrappers copy string arguments
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import os
import shlex
import subprocess
import sys

import vltest_bootstrap

test.scenarios("vlt")

exe = test.obj_dir + "/t_verilated_mt_msg_lifetime"
probe_cpp = test.obj_dir + "/asan_probe.cpp"
probe_exe = test.obj_dir + "/asan_probe"
run_log = test.obj_dir + "/run.log"

cxx_cmd = shlex.split(os.environ["CXX"])
test.write_wholefile(probe_cpp, "int main() { return 0; }\n")
probe_cmd = cxx_cmd + ["-fsanitize=address", "-pthread", probe_cpp, "-o", probe_exe]
if sys.platform == "darwin":
    probe_cmd.append("-Wl,-U,__Z18vlFlushSolverStatsv")
probe = subprocess.run(probe_cmd,
                       stdout=subprocess.DEVNULL,
                       stderr=subprocess.DEVNULL,
                       check=False)
if probe.returncode:
    test.skip("C++ compiler does not support AddressSanitizer")

cmd = [
    *cxx_cmd,
    "-std=gnu++14",
    "-O0",
    "-g",
    "-fsanitize=address",
    "-fno-omit-frame-pointer",
    "-DVL_USER_FATAL",
    "-DVL_USER_FINISH",
    "-DVL_USER_STOP",
    "-DVL_USER_WARN",
    "-I" + os.environ["VERILATOR_ROOT"] + "/include",
    "-I" + os.environ["VERILATOR_ROOT"] + "/include/vltstd",
    "t/t_verilated_mt_msg_lifetime.cpp",
    os.environ["VERILATOR_ROOT"] + "/include/verilated.cpp",
    os.environ["VERILATOR_ROOT"] + "/include/verilated_threads.cpp",
    "-pthread",
    "-o",
    exe,
]
if sys.platform == "darwin":
    cmd.append("-Wl,-U,__Z18vlFlushSolverStatsv")

test.run(cmd=cmd, logfile=test.obj_dir + "/cxx_compile.log")

test.setenv("ASAN_OPTIONS", "abort_on_error=0:detect_leaks=0")
for mode in ("warn", "finish", "stop", "fatal"):
    mode_log = run_log + "." + mode
    test.run(cmd=[exe, mode], logfile=mode_log)
    test.file_grep(mode_log, r"MT_MSG_LIFETIME_DONE " + mode)

test.passes()
