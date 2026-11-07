#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt_all')

test.compile(
    make_top_shell=False,
    make_pli=True,
    threads=2 if test.vltmt else 1,
    v_flags2=["+define+USE_VPI"],
    verilator_flags2=["--binary", "--vpi", "--comp-limit-members", "1", test.pli_filename])

test.execute(use_libvpi=True)

# The force read signal is not in the same struct as its forceable signal
paths = test.file_grep(
    test.obj_dir + "/" + test.vm_prefix + "__Syms__Slow.cpp",
    r'forceableVarInsert\("x", &\(\S+\.TOP\.(\S+)t__DOT__x\),'
    r'.*&\(\S+\.TOP\.(\S+)t__DOT__x__VforceRd\)')
if paths and paths[0] == paths[1]:
    test.error("Force read signal in same struct " + paths[0])

test.passes()
