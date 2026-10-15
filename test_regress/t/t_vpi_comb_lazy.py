#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap
import os

test.scenarios('vlt_all')
test.top_filename = "t/t_vpi_comb.v"
test.golden_filename = "t/t_vpi_comb.out"
test.pli_filename = "t/t_vpi_dump.cpp"

# A small split spreads the syms ctor and the reconstruct bodies over several files.
test.compile(make_top_shell=False,
             make_main=False,
             make_pli=True,
             verilator_flags2=[
                 "--exe --vpi --timing --vpi-lazy --no-l2name --stats --output-split 1"
                 " --output-split-cfuncs 1", test.pli_filename, "t/TestVpiMain.cpp"
             ],
             make_flags=['CPPFLAGS_ADD=-DVL_NO_LEGACY'])

test.execute(use_libvpi=True, expect_filename=test.golden_filename)

test.file_grep(test.stats, r'VPI, lazy reconstructed\s+(\d+)', 39)

# Reconstruction storage follows every eval-path member, off their cache lines
test.file_grep_not(test.obj_dir + "/" + test.vm_prefix + "___024root.h",
                   r'__Vlazy\w*;[\s\S]*\n\s+::(?:[CSIQ]Data|VlWide|VlUnpacked)[^\n;]*\s(?!__Vlazy)\w+;\n')

# Without --vpi-lazy the same design must emit no lazy machinery at all. Verilate only: the
# eager model is t_vpi_comb's.
eager_dir = test.obj_dir + "/obj_eager"
os.makedirs(eager_dir, exist_ok=True)
vlt_cmd = test.compile_vlt_cmd(verilator_flags=["-cc", "-Mdir", eager_dir],
                               verilator_flags2=["--vpi --timing --public-flat-rw"],
                               make_main=False)
test.run(cmd=vlt_cmd, logfile=eager_dir + "/vlt_compile.log", tee=True, verilator_run=True)
test.file_grep_not(eager_dir + "/" + test.vm_prefix + "__Syms__Slow.cpp", r'VLVF_LAZY')

test.passes()
