#!/usr/bin/env python3
# DESCRIPTION: Verilator: Common RepCut regression support
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026-2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import shlex
from pathlib import Path


def clear_model_profiles(test):
    """Discard incompatible model profiles before rebuilding in the same directory."""
    for path in Path(test.obj_dir).glob('*.gcda'):
        path.unlink()


def partitioner(test, membership):
    """Provide controlled test ownership through the external tool protocol."""
    executable = (Path(test.obj_dir) / 'test_partitioner.py').resolve()
    executable.write_text('''#!/usr/bin/env python3
import sys
from pathlib import Path
args = dict(zip(sys.argv[1::2], sys.argv[2::2]))
prefix = Path(args['--graph_file']).name.removesuffix('__repcut_early.graph')
source = Path(''' + repr(str(Path(membership).resolve())) + '''.replace('%p', prefix))
output = Path(args['--work_directory']) / 'rcp_output.txt'
output.write_bytes(source.read_bytes())
''',
                          encoding="utf8")
    executable.chmod(0o755)
    return shlex.quote(str(executable))


def round_robin_partitioner(test):
    """Place sinks in alternating partitions, retaining each dependency closure."""
    executable = (Path(test.obj_dir) / 'test_partitioner.py').resolve()
    executable.write_text('''#!/usr/bin/env python3
import csv
import sys
from pathlib import Path
args = dict(zip(sys.argv[1::2], sys.argv[2::2]))
base = Path(args['--graph_file']).with_suffix('')
with base.with_suffix('.nodes.tsv').open(encoding='utf8') as stream:
    nodes = list(csv.DictReader(stream, delimiter='\\t'))
deps = [[int(x) for x in node['inputs'].split(',') if x] for node in nodes]
with base.with_suffix('.controls.tsv').open(encoding='utf8') as stream:
    for row in csv.DictReader(stream, delimiter='\\t'):
        deps[int(row['node'])].append(int(row['predicate']))
parts = [set() for _ in range(int(args['--nparts']))]
ordinal = 0
for node in nodes:
    if node['kind'] not in ('NEXT', 'OUTPUT', 'MEMWRITE', 'EFFECT', 'CALLBACK'):
        continue
    part = parts[ordinal % len(parts)]
    ordinal += 1
    pending = [int(node['id'])]
    while pending:
        ident = pending.pop()
        if ident not in part:
            part.add(ident)
            pending.extend(deps[ident])
assert set().union(*parts) == set(range(len(nodes)))
output = Path(args['--work_directory']) / 'rcp_output.txt'
output.write_text(''.join(','.join(map(str, sorted(p))) + '\\n' for p in parts), encoding='utf8')
''',
                          encoding="utf8")
    executable.chmod(0o755)
    return shlex.quote(str(executable))
