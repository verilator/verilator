#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('simulator')

test.compile(v_flags2=['t/t_finish_dpi.cpp'],
             verilator_flags2=['--binary', '--stats', 't/t_finish_call_propagation.vlt'])
if test.vlt_all:
    test.file_grep(test.stats, r'Finish, Guards\s+(\d+)', 33)
    test.file_grep(test.stats, r'Finish, Source scopes\s+(\d+)', 24)
    test.file_grep(test.stats, r'Optimizations, Functions inlined\s+(\d+)', 7)
    generated = '\n'.join(
        test.file_contents(filename)
        for filename in test.glob_some(test.obj_dir + f'/{test.vm_prefix}_*.cpp'))
    if '__Vtask_invoke__' not in generated:
        test.error('Expected an inlined invoke task')
    if '__VnoInFunc_direct_recursive' not in generated:
        test.error('Expected a non-inlined recursive task')
for case in ('virtual', 'direct', 'mutual', 'recursive_function', 'interface', 'interface_diamond',
             'extern_virtual', 'extern_function', 'pure_virtual', 'param_function', 'dpi'):
    test.execute(all_run_flags=[f'+CASE={case}'], logfile=test.obj_dir + f'/sim_{case}.log')

if test.vlt_all:
    runtime_obj_dir = test.obj_dir
    runtime_top_shell_filename = test.top_shell_filename
    runtime_v_flags = test.v_flags
    runtime_vm_prefix = test.vm_prefix
    runtime_verilator_flags = test.verilator_flags
    test.obj_dir = runtime_obj_dir + '_public'
    test.v_flags = [flag.replace(runtime_obj_dir, test.obj_dir) for flag in runtime_v_flags]
    test.vm_prefix = 'Vt_finish_public'
    test.verilator_flags = [
        flag.replace(runtime_obj_dir, test.obj_dir) for flag in runtime_verilator_flags
    ]
    test.clean_objs()
    test.mkdir_ok(test.obj_dir)
    test.compile(make_main=False,
                 make_top_shell=False,
                 verilator_flags2=[
                     '--top-module', 'public_top', '--exe', 't/t_finish_user.cpp', '-CFLAGS',
                     '-DVL_USER_FINISH'
                 ],
                 v_flags2=['+define+TEST_PUBLIC'])
    public_generated = '\n'.join(
        test.file_contents(filename)
        for filename in test.glob_some(test.obj_dir + f'/{test.vm_prefix}_*.cpp'))
    function_start = public_generated.find('::public_static_finish(')
    function_end = public_generated.find('\n}\n', function_start)
    function_body = public_generated[function_start:function_end]
    default_return = function_body.find('return {};')
    value_return = function_body.find('return (public_static_finish__Vfuncrtn);')
    if function_start < 0 or function_end < 0 or default_return < 0 or value_return < default_return:
        test.error('Public finish-capable function lacks an ordered default-return epoch guard')
    test.execute(executable=test.obj_dir + '/Vt_finish_public',
                 logfile=test.obj_dir + '/sim_public_user_finish.log')
    test.obj_dir = runtime_obj_dir
    test.top_shell_filename = runtime_top_shell_filename
    test.v_flags = runtime_v_flags
    test.vm_prefix = runtime_vm_prefix
    test.verilator_flags = runtime_verilator_flags

test.passes()
