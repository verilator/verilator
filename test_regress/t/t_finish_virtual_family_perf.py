#!/usr/bin/env python3
# DESCRIPTION: Verilator: Finish virtual-family analysis is linear in class depth
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt')

depth = 128
test.top_filename = f'{test.obj_dir}/in.v'
with open(test.top_filename, 'w', encoding='utf8') as output:
    for index in range(depth):
        extends = '' if index == 0 else f' extends C{index - 1}'
        output.write(f'class C{index}{extends};\n')
        output.write(f'  virtual function void f{index}();\n')
        output.write('  endfunction\n')
        output.write('endclass\n')
    output.write('module t;\n')
    output.write(f'  C{depth - 1} object;\n')
    output.write('  initial object = new;\n')
    output.write('endmodule\n')

test.lint(verilator_flags2=['--stats'])
test.file_grep(test.stats, r'Finish, Virtual family classification visits\s+(\d+)', depth)

test.passes()
