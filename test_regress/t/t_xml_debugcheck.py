#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt')
test.top_filename = "t/t_enum_type_methods.v"

out_filename = test.obj_dir + "/V" + test.name + ".xml"

test.compile(verilator_flags2=['--no-std', '--debug-check', '--flatten'],
             verilator_make_gmake=False,
             make_top_shell=False,
             make_main=False)

test.files_identical(out_filename, test.golden_filename, 'logfile')

# make sure that certain tags are present in --debug-check
# that would not be present in --xml-only
test.file_grep(out_filename, r'<constpool')
test.file_grep(out_filename, r'<inititem')
test.file_grep(out_filename, r'<if')
test.file_grep(out_filename, r'<while')
test.file_grep(out_filename, r'<begin>')  # for <if> and <while>
test.file_grep(out_filename, r' signed=')  # for <basicdtype>
test.file_grep(out_filename, r' func=')  # for <ccall>

test.passes()
