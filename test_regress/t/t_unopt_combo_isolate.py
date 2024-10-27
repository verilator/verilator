#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('simulator')
test.top_filename = "t/t_unopt_combo.v"

out_filename = test.obj_dir + "/V" + test.name + ".tree.json"

test.compile(verilator_flags2=["--no-json-edit-nums +define+ISOLATE --stats"])

if test.vlt_all:
    test.file_grep(test.stats, r'Optimizations, isolate_assignments blocks\s+3')
    test.file_grep(
        out_filename,
        r'{"type":"VAR","name":"t.b",.*"loc":"e,23:[^"]*",.*"origName":"b",.*"attrIsolateAssign":true,.*"dtypeName":"logic"'
    )
    test.file_grep(
        out_filename,
        r'{"type":"VAR","name":"__Vfunc_t.file.get_31_16__0__Vfuncout",.*"loc":"e,99:[^"]*",.*"origName":"__Vfunc_t__DOT__file__DOT__get_31_16__0__Vfuncout",.*"attrIsolateAssign":true,.*"dtypeName":"logic"'
    )
    test.file_grep(
        out_filename,
        r'{"type":"VAR","name":"__Vfunc_t.file.get_31_16__0__t_crc",.*"loc":"e,100:[^"]*",.*"origName":"__Vfunc_t__DOT__file__DOT__get_31_16__0__t_crc",.*"attrIsolateAssign":true,.*"dtypeName":"logic"'
    )
    test.file_grep(
        out_filename,
        r'{"type":"VAR","name":"__Vtask_t.file.set_b_d__1__t_crc",.*"loc":"e,112:[^"]*",.*"origName":"__Vtask_t__DOT__file__DOT__set_b_d__1__t_crc",.*"attrIsolateAssign":true,.*"dtypeName":"logic"'
    )
    test.file_grep(
        out_filename,
        r'{"type":"VAR","name":"__Vtask_t.file.set_b_d__1__t_c",.*"loc":"e,113:[^"]*",.*"origName":"__Vtask_t__DOT__file__DOT__set_b_d__1__t_c",.*"attrIsolateAssign":true,.*"dtypeName":"logic"'
    )

test.execute()

test.passes()
