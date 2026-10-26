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
test.top_filename = "t/t_typename_class.v"

out_filename = test.obj_dir + "/V" + test.name + ".tree.json"

test.compile(verilator_flags2=['--json-only'],
             verilator_make_gmake=False,
             make_top_shell=False,
             make_main=False)

# Classes and interfaces keep the names they had with their parameter types, which are since
# gone, even if another module's type gave one first
test.file_grep(out_filename, r'"dtypeNameFull":"\$unit::TypeP#\(byte\)"')
test.file_grep(out_filename, r'"dtypeNameShort":"TypeP#\(byte\)"')
test.file_grep(out_filename, r'"dtypeNameFull":"tifc#\(byte\)"')
test.file_grep(out_filename, r'"dtypeNameFull":"mcls#\(16\)\.MC"')

test.passes()
