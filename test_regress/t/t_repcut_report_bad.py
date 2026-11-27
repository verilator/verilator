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
base = Path(test.obj_dir) / (test.vm_prefix + '__repcut_early')

for fallback in (False, True):
    test.top_filename = 't/t_repcut_effects.v' if fallback else 't/t_repcut_native.v'
    flags = ['--no-skip-identical', '-fno-dfg']
    if fallback:
        flags += ['-DREPCUT_EFFECT_FALLBACK', '--output-split-cfuncs', '32']
    flags += ['-frepcut']

    cases = [('graph', '*.graph', []), ('plan', '*.plan.tsv', []), ('chunks', '*.chunks.tsv', []),
             ('cuts', '*.cuts.tsv', []), ('publish', '*.publication.tsv', []),
             ('native', '*.native-costs.tsv', ['--debugi-V3RepCutEmit', '3']),
             ('source', '*.source-costs.tsv', ['--debugi-V3RepCutNative', '3'])]
    if fallback:
        cases = [('reject', '*.source-rejected.tree', ['--debugi-V3RepCutNative', '9'])]
    for case, pattern, debug in cases:
        test.compile(verilator_make_gmake=False, verilator_flags2=flags + debug)
        # Discover the emitted path rather than depending on generated kernel IDs.
        report = Path(min(test.glob_some(str(Path(test.obj_dir) / pattern))))
        report.unlink()
        report.mkdir()
        blocker = report / 'blocker'
        blocker.write_text('Keep this directory nonempty during stale-report cleanup.\n',
                           encoding="utf8")
        try:
            test.compile(verilator_make_gmake=False, fails=True, verilator_flags2=flags + debug)
            # Object-directory suffixes vary between harness invocations.
            log = Path(test.obj_dir) / 'vlt_compile.log'
            normalized = Path(test.obj_dir) / (case + '.log')
            normalized.write_text(log.read_text(encoding="utf8").replace(
                test.obj_dir, '@OBJ_DIR@'),
                                  encoding="utf8")
            test.files_identical(str(normalized),
                                 't/' + test.name + '__' + case + '.out',
                                 is_logfile=True)
        finally:
            blocker.unlink()
            report.rmdir()

test.passes()
