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

# V3Param's debug messages name each specialization of a class as it is made, with the values
# of its parameters, before it elaborates any defaults, so these show as '?'
test.lint(verilator_flags2=["--debug --debugi 0 --debugi-V3Param 9"])

test.file_grep(test.compile_log_filename,
               r"nodeDeparamCommon result: 'Foo#\(class Bar#\(class Xyz\),88\)'")
test.file_grep(test.compile_log_filename,
               r"nodeDeparamCommon result: 'Defaults#\(2,virtual interface ifc,\?,3\)'")

test.passes()
