#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2025 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import os
import platform
import vltest_bootstrap

test.scenarios('vlt')

# Two +verilator+vpi+ arguments load two independent libraries: the first
# (t_flag_main_vpi.cpp) observes the design and calls $finish; the second
# (t_flag_main_vpi_lib2.cpp) prints a marker proving it too was loaded.
test.top_filename = 't/t_flag_main_vpi.v'
test.pli_filename = 't/t_flag_main_vpi.cpp'

test.compile(make_pli=True, verilator_flags2=["--binary --vpi --public-flat-rw"])

# Build the second VPI library (make_pli only builds libvpi.so), mirroring the
# driver's own pli flags.
root = os.environ['VERILATOR_ROOT']
pli2_cmd = [os.environ['CXX'], "-I" + root + "/include/vltstd", "-I" + root + "/include", "-fPIC",
            "-shared"]
pli2_cmd += (["-Wl,-undefined,dynamic_lookup"] if platform.system() == 'Darwin' else ["-rdynamic"])
pli2_cmd += ["-o", test.obj_dir + "/libvpi2.so", "t/t_flag_main_vpi_lib2.cpp"]
test.run(logfile=test.obj_dir + "/pli2_compile.log", cmd=pli2_cmd)

test.execute(all_run_flags=[
    "+verilator+vpi+" + test.obj_dir + "/libvpi.so",
    "+verilator+vpi+" + test.obj_dir + "/libvpi2.so"
],
             check_finished=True)

test.file_grep(test.run_log_filename, r'- second VPI library loaded')

test.passes()
