#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026-2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

from pathlib import Path

import vltest_bootstrap

test.scenarios('vlt')
# Internal graph and lowering reports are opt-in.
test.verilator_flags += ['--repcut-dump-graph']
test.top_filename = 't/t_repcut_early.v'
test.compile(verilator_make_gmake=False,
             verilator_flags2=[
                 '-fno-repcut', '--repcut-dump-graph', '--no-skip-identical', '--protect-ids',
                 '--protect-key SECRET_KEY'
             ])
base = test.obj_dir + '/' + test.vm_prefix + '__repcut_early'
test.file_grep(base + '.report.txt', r'complete 1')
test.file_grep_not(base + '.nodes.tsv', r'shared_sum')
test.file_grep_not(base + '.clocks.tsv', r'second_clock_alias|first_clock_alias')
test.file_grep_not(base + '.storage.tsv', r'shared_sum|second_clock_alias|first_clock_alias')
test.file_grep_not(base + '.domains.tsv', r'second_clock_alias|first_clock_alias')

test.top_filename = 't/t_repcut_early_partial.v'
test.compile(verilator_make_gmake=False,
             verilator_flags2=[
                 '-fno-repcut', '--repcut-dump-graph', '--no-skip-identical', '--protect-ids',
                 '--protect-key SECRET_KEY', '+define+REPCUT_MEMORY_ODD'
             ])
assert 'complete 1' in Path(base + '.report.txt').read_text(encoding="utf8")
assert '__DOT__mem' not in Path(base + '.nodes.tsv').read_text(encoding="utf8")
assert '__DOT__mem' not in Path(base + '.memories.tsv').read_text(encoding="utf8")
assert '__Vxrand' not in Path(base + '.nodes.tsv').read_text(encoding="utf8")
for suffix in ('.storage.tsv', '.domains.tsv', '.bindings.tsv'):
    contents = Path(base + suffix).read_text(encoding="utf8")
    assert '__DOT__mem' not in contents
    assert '__Vxrand' not in contents
test.compile(verilator_make_gmake=False,
             verilator_flags2=[
                 '--repcut', '--no-skip-identical', '--protect-ids', '--protect-key', 'SECRET_KEY',
                 '+define+REPCUT_MEMORY_ODD'
             ])
for suffix in ('.plan.tsv', '.owners.tsv'):
    contents = Path(base + suffix).read_text(encoding="utf8")
    assert '__DOT__mem' not in contents
    assert '__Vxrand' not in contents
for path in Path(test.obj_dir).iterdir():
    if path.suffix in ('.cpp', '.h'):
        contents = path.read_text(encoding="utf8")
        assert '__DOT__mem' not in contents
        assert '__Vxrand' not in contents
test.passes()
