#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import re

import vltest_bootstrap

test.scenarios('vlt')
test.top_filename = 't/t_covergroup_scope.v'

# The names of covergroup types include the names of their scopes, which must be obfuscated,
# and get_coverage() must find each type's instances under its obfuscated name
test.compile(
    verilator_flags2=['--coverage', '--protect-ids', '--protect-key SCOPE_KEY', '-Wno-INSECURE'])
test.execute()


# A name as Verilator encodes it into a C++ identifier, AstNode::encodeName(), for names without
# '__', as these
def encode(name):
    out = ""
    for i, c in enumerate(name):
        if c.isalpha() or (i and c.isdigit()) or c == '_':
            out += c
        else:
            out += "__0%02x" % ord(c)
    return out


# The scopes naming the covergroup types of t_covergroup_scope.v, as written there.  Each must
# appear neither as written, as the coverage database and strings would hold it, nor encoded, as
# the identifiers of generated C++ would, which differs for escaped identifiers, as 'cg+symbol'.
names = ('First', 'Second', 'Holder', 'Param', 'Untyped', 'Outer', 'inner', 'sub_a', 'sub_b',
         'sub_e', 'sub_p', 'gen_e', 'gen_esc', 'gen_esc.cg', 'Klass!', 'cg+symbol', 'cg@symbol2',
         'pack+gen', '$unit')
scopes = '|'.join(sorted({re.escape(form) for name in names for form in (name, encode(name))}))
test.file_grep_not(test.coverage_filename, scopes)
for filename in test.glob_some(test.obj_dir + '/*.cpp'):
    test.file_grep_not(filename, scopes)

test.passes()
