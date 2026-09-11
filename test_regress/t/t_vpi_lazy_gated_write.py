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
test.top_filename = "t/t_vpi_lazy_gated_write.v"

test.compile(make_top_shell=False,
             make_main=False,
             verilator_flags2=["--exe --vpi --vpi-lazy --no-l2name --stats", test.pli_filename])

test.execute()

# Retained signals carry storage; the runtime write gate keys off them.
test.file_grep(test.obj_dir + "/" + test.vm_prefix + "__Syms__Slow.cpp", r'VLVF_LAZY_RETAINED')

# The deposit flag is read and cleared in one place, so a deposit settles exactly once.
test.file_grep(
    test.obj_dir + "/" + test.vm_prefix + ".cpp",
    r'bool ' + test.vm_prefix + r'::evalNeedsSettle\(\) \{\n'
    r'\s*const bool needsSettle = vlSymsp->__Vm_vpiLazyWritten;\n'
    r'\s*vlSymsp->__Vm_vpiLazyWritten = false;\n')
test.file_grep_count(test.obj_dir + "/" + test.vm_prefix + ".cpp", r'__Vm_vpiLazyWritten', 2)

# A retained signal is not itself a scheduler input, and aliases of the top-level ports are
# reconstructed rather than retained, so no input logic is replicated at all.
# --public-flat-rw replicates 56 statements here.
test.file_grep(test.obj_dir + "/" + test.vm_prefix + "__stats.txt",
               r'size of replicated logic: Input\s+0')

test.passes()
