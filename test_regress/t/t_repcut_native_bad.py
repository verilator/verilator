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

test.scenarios('vltmt')
# Internal graph and lowering reports are opt-in.
test.verilator_flags += ['--repcut-dump-graph']
test.top_filename = 't/t_repcut_native.v'
directory = Path(test.obj_dir)
base = directory / (test.vm_prefix + '__repcut_early')
work = Path(str(base) + '.partition')
work.mkdir(exist_ok=True)
membership = work / 'rcp_output.txt'
partitioner = directory / 'partitioner.py'
for case, body in (('missing', None), ('exit', 'raise SystemExit(7)'), ('stale', 'pass'),
                   ('malformed', "out.write_text('bogus\\n')"),
                   ('count', "out.write_text(','.join(map(str, range(nodes))) + '\\n')"),
                   ('removed', None), ('removed_decoder', None), ('removed_alias', None),
                   ('removed_no_alias', None), ('locked', None)):
    # A failed/no-output invocation must never import a previous successful plan.
    membership.write_text('stale output must not survive\n', encoding="utf8")
    executable = str(directory / 'missing-partitioner')
    if body is not None:
        partitioner.write_text('''#!/usr/bin/env python3
import sys
from pathlib import Path
args = dict(zip(sys.argv[1::2], sys.argv[2::2]))
out = Path(args['--work_directory']) / 'rcp_output.txt'
nodes = int(Path(args['--graph_file']).read_text().splitlines()[0].split()[1])
''' + body + '\n',
                               encoding="utf8")
        partitioner.chmod(0o755)
        executable = str(partitioner.resolve())
    flags = ['-frepcut', '--repcut-partitioner', executable, '--no-skip-identical']
    if case == 'locked':
        flags = ['-frepcut', '--no-skip-identical']
        (work / '.lock').write_text('held by regression\n', encoding='utf8')
    if case == 'removed':
        flags = ['--repcut-partitions', 'unused.csv']
    elif case == 'removed_decoder':
        flags = ['--repcut-private-decoders']
    elif case == 'removed_alias':
        flags = ['--repcut']
    elif case == 'removed_no_alias':
        flags = ['--no-repcut']
    else:
        for suffix in ('.plan.tsv', '.owners.tsv', '.chunks.tsv', '.cuts.tsv'):
            Path(str(base) + suffix).write_text('stale accepted plan', encoding="utf8")
    test.compile(verilator_make_gmake=False, fails=True, threads=2, verilator_flags2=flags)
    if case == 'locked':
        (work / '.lock').unlink()
    log = directory / 'vlt_compile.log'
    normalized = directory / (case + '.log')
    normalized.write_text(log.read_text(encoding="utf8").replace(test.obj_dir, '@OBJ_DIR@'),
                          encoding="utf8")
    test.files_identical(str(normalized), 't/' + test.name + '__' + case + '.out', is_logfile=True)
    if case in ('missing', 'exit', 'stale', 'locked'):
        assert not membership.exists(), case
    for suffix in ('.plan.tsv', '.owners.tsv', '.chunks.tsv', '.cuts.tsv'):
        assert not Path(str(base) + suffix).exists(), (case, suffix)
test.passes()
