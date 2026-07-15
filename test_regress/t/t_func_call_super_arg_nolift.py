#!/usr/bin/env python3
# DESCRIPTION: Verilator: Super constructor finish propagation without expression lifting
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt')
test.top_filename = 't/t_func_call_super_arg.v'

test.compile(verilator_flags2=['--no-timing', '-fno-lift-expr'])

guarded_sibling_re = (r'(?s)\(\[&\]\(\)[^{]*\{\s*'
                      r'if\s*\((?=[^{};]*finishEpoch\(\))(?=[^{};]*!=)[^{};]*\)\s*\{\s*'
                      r'return\s+\{\};\s*\}\s*'
                      r'(?:(?!\}\s*\(\)).)*?'
                      r'(?:__VnoInFunc_sibling_argument|__PVT__sibling_calls)')

for class_name in ('derived_mixed', 'derived_mixed_reverse'):
    files = test.glob_some(test.obj_dir + '/' + test.vm_prefix + '*' + class_name +
                           '__Vclpkg*.cpp')
    test.file_grep_any(files, guarded_sibling_re)

for mode in ('base', 'argument', 'caller_argument', 'nested_argument', 'conditional_argument',
             'conditional_complete', 'callback_argument', 'multiple_arguments',
             'non_finishing_argument', 'mixed_arguments', 'mixed_arguments_reverse',
             'default_argument', 'default_super_argument', 'writable_sibling', 'writable_complete',
             'writable_guarded_complete', 'inout_complete', 'inout_sibling',
             'inout_guarded_complete', 'ref_sibling', 'ref_complete', 'ref_complex',
             'ref_complex_reverse', 'ref_complex_complete', 'ref_complex_index_finish',
             'ref_queue_complete', 'const_ref_sibling', 'const_ref_complex',
             'const_ref_complex_reverse', 'const_ref_complex_complete',
             'const_ref_complex_index_finish', 'constructor_chain'):
    test.execute(all_run_flags=[f'+MODE={mode}'], logfile=test.obj_dir + f'/sim_{mode}.log')

test.passes()
