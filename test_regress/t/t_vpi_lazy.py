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

test.scenarios('vlt')

test.compile(make_top_shell=False,
             make_main=False,
             verilator_flags2=[
                 "--exe --vpi --vpi-lazy --no-l2name --stats -Wno-MULTIDRIVEN", test.pli_filename
             ])

test.execute()

test.file_grep(test.stats, r'VPI, lazy reconstructed\s+(\d+)', 40)
test.file_grep(test.stats, r'VPI, lazy groups\s+(\d+)', 27)
test.file_grep(test.stats, r'VPI, lazy copy descriptors\s+(\d+)', 10)
test.file_grep(test.stats, r'VPI, lazy fallback retained\s+(\d+)', 8)
test.file_grep(test.stats, r'VPI, lazy floor retained\s+(\d+)', 5)
test.file_grep(test.stats, r'VPI, lazy group bail, completeness floor\s+(\d+)', 5)
test.file_grep(test.stats, r'VPI, lazy group bail, latch\s+(\d+)', 1)
test.file_grep(test.stats, r'VPI, lazy group bail, multidriven\s+(\d+)', 1)
test.file_grep(test.stats, r'VPI, lazy group bail, partial overlap\s+(\d+)', 1)
test.file_grep(test.stats, r'VPI, lazy group bail, read before write\s+(\d+)', 1)
test.file_grep(test.stats, r'VPI, lazy floor residual, sequential\s+(\d+)', 4)
test.file_grep(test.stats, r'VPI, lazy public rw variables\s+(\d+)', 3)

syms = test.obj_dir + "/" + test.vm_prefix + "__Syms__Slow.cpp"

test.file_grep(syms, r'VLVF_LAZY_PUBLIC_RW')
test.file_grep(syms, r'__Vm_lazyReconstructDatap')

# Aliases of the flop 'keep' reconstruct into shadows of their own, each with its own row;
# pointing their rows at keep's storage would leak a deposit into the counter.
test.file_grep(syms, r'\{"alias1", offsetof\(\S+ __Vlazyrecon__\d+_\d+\).*VLVF_LAZY_PUBLIC_RW')
test.file_grep(syms, r'\{"alias2", offsetof\(\S+ __Vlazyrecon__\d+_\d+\).*VLVF_LAZY_PUBLIC_RW')
test.file_grep(syms, r'\{"port_out", offsetof\(\S+ __Vlazyrecon__\d+_\d+\)')
test.file_grep_not(syms, r'\{"alias\d", offsetof\(\S+ t__DOT__keep\)')
test.file_grep(test.obj_dir + "/" + test.vm_prefix + "__Syms.h", r'__Vlazy_reconstruct')

# Without --vpi-lazy the same design must emit no lazy machinery at all. Verilate only: the
# eager model has no testbench of its own here.
eager_dir = test.obj_dir + "/obj_eager"
os.makedirs(eager_dir, exist_ok=True)
vlt_cmd = test.compile_vlt_cmd(verilator_flags=["-cc", "-Mdir", eager_dir],
                               verilator_flags2=["--vpi --public-flat-rw -Wno-MULTIDRIVEN"],
                               make_main=False)
test.run(cmd=vlt_cmd, logfile=eager_dir + "/vlt_compile.log", tee=True, verilator_run=True)

eager_syms = eager_dir + "/" + test.vm_prefix + "__Syms__Slow.cpp"
test.file_grep_not(eager_syms, r'__VlazyDatap_')
test.file_grep_not(eager_syms, r'VLVF_LAZY_PUBLIC_RW')

test.passes()
