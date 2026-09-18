#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap
import glob

test.scenarios('vlt')

test.top_filename = "t/t_vpi_lazy.v"
test.pli_filename = "t/t_vpi_lazy.cpp"

# A small split spreads the syms ctor and the reconstruct bodies over several files.
test.compile(make_top_shell=False,
             make_main=False,
             verilator_flags2=[
                 "--exe --vpi --vpi-lazy --no-l2name --output-split 1 --output-split-cfuncs 1"
                 " -Wno-MULTIDRIVEN", test.pli_filename
             ])

test.execute()

syms = test.obj_dir + "/" + test.vm_prefix + "__Syms__Slow.cpp"
srcs = test.glob_some(test.obj_dir + "/" + test.vm_prefix + "*.cpp")

# The recon-fn arrays must not be local to whichever split file got the syms ctor.
test.file_grep(syms, r'^extern const VlLazyReconEntry \S+__VlazyReconFns\d+\[\] = \{')
# Declared extern in the syms header, so no split TU gets a local copy.
test.file_grep(test.obj_dir + "/" + test.vm_prefix + "__Syms.h",
               r'extern const VlLazyReconEntry \S+__VlazyReconFns\d+\[\];')
for f in test.glob_some(test.obj_dir + "/" + test.vm_prefix + "__Syms__ctor__*.cpp"):
    test.file_grep_not(f, r'extern const VlLazyReconEntry \S+__VlazyReconFns\d+\[\];')

# Same rule for the VPI var tables, which is a different symbol and so was not covered by the
# grep above: re-declaring these per split TU was 21% of VeeR-EL2's generated lines.
test.file_grep(test.obj_dir + "/" + test.vm_prefix + "__Syms.h", r'extern const VlVarTableEntry')
# glob_some() errors when a pattern matches nothing, and a design need not split its dtor.
for f in (test.glob_some(test.obj_dir + "/" + test.vm_prefix + "__Syms__ctor__*.cpp") +
          glob.glob(test.obj_dir + "/" + test.vm_prefix + "__Syms__dtor__*.cpp")):
    test.file_grep_not(f, r'extern const VlVarTableEntry \S+\[\];')

# The reconstruct body was split, so the memo must not live inside it.
test.file_grep_any(
    srcs, r'void ' + test.vm_prefix + r'___024root__' + r'__Vlazy_reconstruct_body__\d+__\d+\(')

# The compare, the restamp and the body call must stay together in whichever function the
# split leaves them in; separating them would make the memo inert.
test.file_grep_any(
    srcs,
    r'void ' + test.vm_prefix + r'___024root____Vlazy_reconstruct__(\d+)(?:__\d+)?\([^)]*\) \{\n'
    r'(?:.*\n)*?\s*if \(+(?:vlSelf->|vlSelfRef\.)__Vlazyepoch\[\1U?\]'
    r' != vlSymsp->__Vm_lazyEpoch\)+ \{\n'
    r'\s*(?:vlSelf->|vlSelfRef\.)__Vlazyepoch\[\1U?\] = vlSymsp->__Vm_lazyEpoch;\n'
    r'\s*' + test.vm_prefix + r'___024root____Vlazy_reconstruct_body__\1\(')

test.passes()
