#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2024 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import json
import vltest_bootstrap

test.scenarios('vlt')
test.top_filename = "t/t_enum_type_methods.v"

out_filename = test.obj_dir + "/V" + test.name + ".tree.json"

test.compile(verilator_flags2=[
    '--no-std', '--debug-check', '--no-json-edit-nums', '--flatten', '--inline-cfuncs', '0'
],
             verilator_make_gmake=False,
             make_top_shell=False,
             make_main=False)

# not files_identical as output is too sensitive to internal changes
test.file_grep(out_filename, r'"type":"MODULE"')

# check JSON is parsable
with open(out_filename, 'r', encoding="utf8") as fh:
    json.load(fh)

test.passes()
