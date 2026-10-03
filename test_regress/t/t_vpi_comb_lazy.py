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

test.compile(make_top_shell=False,
             make_main=False,
             make_pli=True,
             verilator_flags2=[
                 "--exe --vpi --timing --vpi-lazy --no-l2name --stats", test.pli_filename,
                 "t/TestVpiMain.cpp"
             ],
             make_flags=['CPPFLAGS_ADD=-DVL_NO_LEGACY'])

test.execute(use_libvpi=True, expect_filename=test.golden_filename)

test.file_grep(test.stats, r'VPI, lazy reconstructed\s+(\d+)', 39)
test.file_grep(test.stats, r'VPI, lazy groups\s+(\d+)', 28)
test.file_grep(test.stats, r'VPI, lazy copy descriptors\s+(\d+)', 8)
test.file_grep(test.stats, r'VPI, lazy fallback retained\s+(\d+)', 9)
test.file_grep(test.stats, r'VPI, lazy floor retained\s+(\d+)', 15)
test.file_grep(test.stats, r'VPI, lazy group bail, latch\s+(\d+)', 1)
test.file_grep(test.stats, r'VPI, lazy group bail, multidriven\s+(\d+)', 1)
test.file_grep(test.stats, r'VPI, lazy group bail, partial overlap\s+(\d+)', 1)
test.file_grep(test.stats, r'VPI, lazy group bail, read before write\s+(\d+)', 1)
test.file_grep(test.stats, r'VPI, lazy floor residual, sequential\s+(\d+)', 4)
test.file_grep(test.stats, r'VPI, lazy floor residual, storage pinned\s+(\d+)', 2)

syms = test.obj_dir + "/" + test.vm_prefix + "__Syms__Slow.cpp"

test.file_grep(syms, r'VLVF_LAZY_REMAT')
test.file_grep(syms, r'__Vm_lazyReconstructDatap')

# Aliases of the flop 'keep' are copy rows with shadows of their own, as each alias has storage
# of its own under --public-flat-rw.
test.file_grep(syms, r'\{"alias1", offsetof\(\S+ __Vlazyrecon__\d+_\d+\).*VLVF_LAZY_REMAT')
test.file_grep(syms, r'\{"alias2", offsetof\(\S+ __Vlazyrecon__\d+_\d+\).*VLVF_LAZY_REMAT')
test.file_grep(syms, r'\{"port_out", offsetof\(\S+ __Vlazyrecon__\d+_\d+\)')
test.file_grep_not(syms, r'\{"alias\d", offsetof\(\S+ t__DOT__keep\)')
test.file_grep(test.obj_dir + "/" + test.vm_prefix + "__Syms.h", r'__Vlazy_reconstruct')

# Without --vpi-lazy the same design must emit no lazy machinery at all. Verilate only: the
# eager model is t_vpi_comb's.
eager_dir = test.obj_dir + "/obj_eager"
os.makedirs(eager_dir, exist_ok=True)
vlt_cmd = test.compile_vlt_cmd(verilator_flags=["-cc", "-Mdir", eager_dir],
                               verilator_flags2=["--vpi --timing --public-flat-rw"],
                               make_main=False)
test.run(cmd=vlt_cmd, logfile=eager_dir + "/vlt_compile.log", tee=True, verilator_run=True)

eager_syms = eager_dir + "/" + test.vm_prefix + "__Syms__Slow.cpp"
test.file_grep_not(eager_syms, r'__VlazyDatap_')
test.file_grep_not(eager_syms, r'VLVF_LAZY_REMAT')

test.passes()
