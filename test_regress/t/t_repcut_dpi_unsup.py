#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026-2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import csv
from pathlib import Path

import vltest_bootstrap

test.scenarios('vlt')
# Internal graph and lowering reports are opt-in.
test.verilator_flags += ['--repcut-dump-graph']
base = Path(test.obj_dir) / (test.vm_prefix + '__repcut_early')
# Native capture accepts private memory updates but preserves shared blocking,
# context/reentrant and combinational foreign boundaries.
for mode, captures in (('CONTEXT', 0), ('SHARED', 0), ('MEMORY', 1), ('COMBO', 0)):
    test.compile(make_main=False,
                 verilator_make_gmake=False,
                 verilator_flags2=['-fno-repcut', '--repcut-dump-graph', '+define+' + mode])
    assert 'complete 1\n' in base.with_suffix('.report.txt').read_text(encoding="utf8")
    with base.with_suffix('.nodes.tsv').open(encoding="utf8") as stream:
        nodes = list(csv.DictReader(stream, delimiter='\t'))
    assert sum(n['kind'] == 'CALLBACK' for n in nodes) == captures, mode

test.passes()
