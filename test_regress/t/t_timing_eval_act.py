#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2026 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt')

test.compile(verilator_flags2=["--binary", "--runtime-debug"])

test.file_grep(
    test.obj_dir + "/" + test.vm_prefix + "___024root__0.cpp", r'void\s+' + test.vm_prefix +
    r'___024root___timing_resume\(' + test.vm_prefix + r'___024root\*\s+vlSelf\)\s+\{' +
    r'\n((?!})(.|\n))*' + r'\/\*' + test.top_filename + r':18\s0x[0-9a-f]+\*\/\s*' +
    r'vlSelfRef\.__VtrigSched_[\d\w]*\.resume\([\n\s]*\"@\(\[event\]\st\.a\)\"\);\n\s+' + r'\/\*' +
    test.top_filename + r':19\s0x[0-9a-f]+\*\/\s*' +
    r'vlSelfRef\.__VtrigSched_[\d\w]*\.resume\([\n\s]*\"@\(posedge\st\.clk_inv\)\"\);\n\s+' +
    r'\/\*' + test.top_filename + r':20\s0x[0-9a-f]+\*\/\s*' +
    r'vlSelfRef\.__VtrigSched_[\d\w]*\.resume\([\n\s]*\"@\(\[event\]\st\.e\)\"\);')

test.execute(all_run_flags=["+verilator+debug"], expect_filename=test.golden_filename)

test.passes()
