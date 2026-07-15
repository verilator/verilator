#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt_all')

modes = ('begin', 'constructor', 'join', 'join_any', 'join_none', 'wait_fork', 'delay', 'event',
         'wait_loop', 'lambda')


def compile_execute():
    test.compile(verilator_flags2=[
        '--binary', '--stats', '--timing', '-Wno-ASSIGNEQEXPR', '-Wno-FUNCTIMECTL'
    ],
                 threads=(2 if test.vltmt else 1))
    test.file_grep(test.stats, r'Timing, Finish guards\s+(\d+)', 33)
    generated = '\n'.join(
        test.file_contents(filename)
        for filename in test.glob_some(test.obj_dir + f'/{test.vm_prefix}___024root__*.cpp'))
    fork_coroutines = []
    for chunk in generated.split('\nVlCoroutine ')[1:]:
        signature = chunk.split('\n', 1)[0]
        if signature.endswith(') {') and 'VlForkSync __Vfork_' in signature:
            fork_coroutines.append(chunk)
    if not fork_coroutines:
        test.error('No generated fork coroutines found')
    for body in fork_coroutines:
        done_pos = body.find('__sync.done(')
        finished_pos = body.find('vlProcess->state(VlProcess::FINISHED);', done_pos)
        return_pos = body.find('co_return;', finished_pos)
        if done_pos < 0 or finished_pos < done_pos or return_pos < finished_pos:
            test.error('Fork coroutine does not preserve done/finished epilogue ordering')
        last_label_pos = body.rfind('__Vlabel', 0, return_pos)
        if 'finishEpoch()' in body and (last_label_pos < 0 or last_label_pos > done_pos):
            test.error('Finish-capable fork coroutine exits after its synchronization epilogue')
    for mode in modes:
        test.execute(all_run_flags=[f'+MODE={mode}'], logfile=test.obj_dir + f'/sim_{mode}.log')


compile_execute()

test.passes()
