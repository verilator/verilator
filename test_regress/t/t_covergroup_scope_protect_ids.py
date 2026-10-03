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
test.top_filename = 't/t_covergroup_scope.v'

# The names of covergroup types include the names of their scopes, which must be obfuscated,
# and get_coverage() must find each type's instances under its obfuscated name
test.compile(
    verilator_flags2=['--coverage', '--protect-ids', '--protect-key SCOPE_KEY', '-Wno-INSECURE'])
test.execute()

scopes = r'First|Second|Holder|Param|Outer|inner|sub_a|sub_b|sub_e|sub_p|gen_e|Klass|cg.symbol|cg__02bsymbol|symbol2|pack.gen|pack__02bgen|\$unit'
test.file_grep_not(test.coverage_filename, scopes)
for filename in test.glob_some(test.obj_dir + '/*.cpp'):
    test.file_grep_not(filename, scopes)

test.passes()
